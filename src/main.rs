use std::{
    collections::BTreeSet,
    io::{self, BufRead},
};

use cryptominisat::{Lbool, Lit, Solver};
use indexmap::IndexSet;
use Lbool::{False, True, Undef};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum VarName {
    UserVar(isize),
    Clause(usize),
    Chain(usize),
}

fn user_var_name(var_map: &IndexSet<VarName>, index: usize, value: bool) -> isize {
    if let Some(&VarName::UserVar(user_var)) = var_map.get_index(index) {
        if value {
            user_var
        } else {
            -user_var
        }
    } else {
        panic!("not a user var");
    }
}

fn main() -> anyhow::Result<()> {
    // Maintains conjunction of clauses
    let mut pos_solver = Solver::new();
    // Maintains disjunction of negated clauses
    let mut neg_solver = Solver::new();

    // Map user variables into internal variables, so we have space for auxiliary variables
    let mut var_map = IndexSet::<VarName>::default();

    let stdin = io::stdin();
    let mut clause_counter = 0;

    // Literal used to incrementally extend the disjunction in `neg_solver`
    let mut chain: Option<Lit> = None;

    for line in stdin.lock().lines() {
        let line = line?;

        // Parse a clause
        let mut clause = vec![];
        for lit_str in line.split_ascii_whitespace() {
            let lit_val = str::parse::<isize>(lit_str)?;
            if lit_val == 0 {
                break;
            }

            let (index, _) = var_map.insert_full(VarName::UserVar(lit_val.abs()));

            let var = Lit::new(index as u32, false).unwrap();
            clause.push(if lit_val < 0 { !var } else { var });
        }

        // We use an emtpy clause to request solving
        if clause.is_empty() {
            // First we find a full model using `pos_solver`
            match pos_solver.solve() {
                True => {
                    // If we find one, we initialize our assumptions with the full model
                    let model = pos_solver.get_model();
                    let mut assumptions = vec![];
                    print!("full model: ");
                    for (index, &var_name) in var_map.iter().enumerate() {
                        if let VarName::UserVar(_) = var_name {
                            print!("{} ", user_var_name(&var_map, index, model[index] == True));
                            assumptions
                                .push(!Lit::new(index as u32, model[index] != True).unwrap());
                        }
                    }
                    println!();

                    if let Some(chain) = chain {
                        // We force at least one of the negated clauses in `neg_solver` to be true
                        // by assuming `chain`
                        let mut essential = BTreeSet::new();
                        essential.insert(chain);

                        // We then remove one literal of our current model (essential + assumptions)
                        // and see if it can be extended to falsify a clause
                        while let Some(candidate) = assumptions.pop() {
                            let assumption_len = assumptions.len();
                            println!(
                                "solving... {}/{}",
                                essential.len() - 1,
                                essential.len() - 1 + assumptions.len()
                            );
                            assumptions.extend(essential.iter().cloned());
                            if neg_solver.solve_with_assumptions(&assumptions) == True {
                                // If it can be falsified our candidate is essential
                                assumptions.truncate(assumption_len);
                                essential.insert(candidate);
                            } else {
                                // Otherwise the candidate isn't needed and the solver produces a
                                // subset of failed literals which we use to update `assumptions`
                                // (removing literals we already know to be `essential`)
                                assumptions.clear();
                                assumptions.extend(
                                    neg_solver
                                        .get_conflict()
                                        .iter()
                                        .map(|&lit| !lit)
                                        .filter(|lit| !essential.contains(lit)),
                                );
                            }
                        }

                        // The user isn't interested in our auxiliary variable
                        essential.remove(&chain);

                        print!("reduced model: ");
                        for lit in &essential {
                            let index = lit.var() as usize;
                            print!("{} ", user_var_name(&var_map, index, model[index] == True));
                        }
                        clause.clear();

                        println!();

                        println!("blocking reduced model");
                        clause.extend(essential);
                    } else {
                        println!("no clauses");
                    }
                }
                False => {
                    println!("unsat");
                    break;
                }
                Undef => {
                    unreachable!()
                }
            }
        }

        for solver in &mut [&mut pos_solver, &mut neg_solver] {
            // Since when did cryptominisat require declaring variables with new_var?
            while (solver.nvars() as usize) <= var_map.len() + 2 {
                solver.new_var();
            }
        }

        // We can directly add the clause to `pos_solver`

        pos_solver.add_clause(&clause);
        clause_counter += 1;

        // For `neg_solver` we add an auxiliary variable that will be true when the clause is
        // falsified.
        let (index, _) = var_map.insert_full(VarName::Clause(clause_counter));
        let clause_indicator = Lit::new(index as u32, false).unwrap();

        // We update the `chain` variable such that it is a conjunction of all clauses so far
        if let Some(prev_chain) = chain {
            let (index, _) = var_map.insert_full(VarName::Chain(clause_counter));
            let next_chain = Lit::new(index as u32, false).unwrap();

            // next_chain = prev_chain | clause_indicator
            neg_solver.add_clause(&[!prev_chain, next_chain]);
            neg_solver.add_clause(&[!clause_indicator, next_chain]);
            neg_solver.add_clause(&[clause_indicator, prev_chain, !next_chain]);
            chain = Some(next_chain);
        } else {
            chain = Some(clause_indicator);
        }

        // clause_indicator = !lit_0 & ... & lit_n
        for lit in &mut clause {
            neg_solver.add_clause(&[*lit, !clause_indicator]);
            *lit = !*lit;
        }
        clause.push(clause_indicator);
        neg_solver.add_clause(&clause);
    }

    Ok(())
}
