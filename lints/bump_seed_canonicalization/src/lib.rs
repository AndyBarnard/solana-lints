#![feature(rustc_private)]
#![feature(box_patterns)]
#![warn(unused_extern_crates)]

use if_chain::if_chain;
use rustc_lint::{LateContext, LateLintPass};
use rustc_hir::{
    Body
};

use rustc_middle::{
    mir,
    mir::terminator::TerminatorKind,
    ty::TyKind,
    mir::{Place, Rvalue, Operand, BasicBlock, StatementKind, ProjectionElem, Local, AggregateKind}
};

use clippy_utils::{
    diagnostics::span_lint, match_def_path
};
mod paths;

extern crate rustc_hir;
extern crate rustc_middle;

dylint_linting::impl_late_lint! {
    /// **What it does:**
    /// Finds uses of solana_program::program::invoke that do not check the bump_seed
    ///
    /// **Why is this bad?**
    /// A contract could call into an attacker-controlled contract instead of the intended one
    ///
    /// **Known problems:**
    /// False positives, since the bump_seed check may be within some other function (does not
    /// trace through function calls)
    /// False negatives, since our analysis is not path-sensitive (the bump_seed check may not
    /// occur in all possible execution paths)
    ///
    /// **Example:**
    ///
    /// ```rust
    /// // example code where a warning is issued
    /// let ix = Instruction {
    ///   bump_seed: *program_id,
    ///   accounts: vec![AccountMeta::new_readonly(*bump_seed, false)],
    ///   data: vec![0; 16],
    /// };
    /// invoke(&ix, accounts.clone());
    ///
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code that does not raise a warning
    /// if (*bump_seed == ...) {
    ///     ...
    /// }
    /// let ix = Instruction {
    ///   bump_seed: *program_id,
    ///   accounts: vec![AccountMeta::new_readonly(*bump_seed, false)],
    ///   data: vec![0; 16],
    /// };
    /// invoke(&ix, accounts.clone());
    /// ```
    pub BUMP_SEED_CANONICALIZATION,
    Warn,
    "Finds unconstrained inter-contract calls",
    BumpSeedCanonicalization::default()
}

#[derive(Default)]
struct BumpSeedCanonicalization {
}

impl<'tcx> LateLintPass<'tcx> for BumpSeedCanonicalization {
    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx Body<'tcx>) {
        let hir_map = cx.tcx.hir();
        let body_did = hir_map.body_owner_def_id(body.id()).to_def_id();
        if !cx.tcx.def_kind(body_did).is_fn_like() {
            return;
        }
        assert!(cx.tcx.is_mir_available(body_did));
        let body_mir = cx.tcx.optimized_mir(body_did);
        let terminators = body_mir.basic_blocks().iter_enumerated().map(|(block_id, block)| (block_id, &block.terminator));
        for (_idx, (block_id, terminator)) in terminators.enumerate() {
            if_chain! {
                if let t = terminator.as_ref().unwrap();
                if let TerminatorKind::Call { func: func_operand, args, destination: _, cleanup: _, .. } = &t.kind;
                if let mir::Operand::Constant(box func) = func_operand;
                if let TyKind::FnDef(def_id, _callee_substs) = func.literal.ty().kind();
                then {
                    // Static call
                    let callee_did = *def_id;
                    if match_def_path(cx, callee_did, &paths::CREATE_PROGRAM_ADDRESS) {
                        let seed_arg = &args[0];
                        if let Operand::Move(p) = seed_arg {
                            let likely_bump_locals: Vec<Local> = self.find_bump_seed_for_seed_array(cx, body_mir, block_id, p).iter().map(|pl| pl.local).collect();
                            if !self.is_bump_seed_checked(cx, body_mir, block_id, likely_bump_locals) {
                                span_lint(
                                    cx,
                                    BUMP_SEED_CANONICALIZATION,
                                    t.source_info.span,
                                    "bump seed may not be constrained",
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

impl BumpSeedCanonicalization {
    fn find_bump_seed_for_seed_array<'tcx>(&self, cx: &LateContext, body: &'tcx mir::Body<'tcx>, block: BasicBlock, mut seeds_arg: &Place<'tcx>) -> Vec<Place<'tcx>> {
        let preds = body.predecessors();
        let bbs = body.basic_blocks();
        let mut cur_block = block;
        let mut found_bump_seed = false;
        let mut likely_bump_seed_aliases = Vec::<Place>::new();
        loop {
            // check every statement
            for stmt in bbs[cur_block].statements.iter().rev() {
                if let StatementKind::Assign(box (assign_place, rvalue)) = &stmt.kind {
                    // trace assignments so we have a list of locals that contain the bump_seed
                    if assign_place.local_or_deref_local() == seeds_arg.local_or_deref_local() {
                        println!("match: {:?}", stmt);
                        match rvalue {
                            Rvalue::Use(Operand::Copy(rvalue_place) | Operand::Move(rvalue_place)) => {
                                println!("Found assignment {:?}", stmt);
                                seeds_arg = rvalue_place;
                                if found_bump_seed {
                                    likely_bump_seed_aliases.push(*rvalue_place);
                                }
                            },
                            Rvalue::Ref(_, _, pl) => {
                                println!("Found assignment (ref) {:?}", pl);
                                seeds_arg = pl;
                                if found_bump_seed {
                                    likely_bump_seed_aliases.push(*seeds_arg);
                                }
                            },
                            Rvalue::Cast(_, Operand::Copy(rvalue_place) | Operand::Move(rvalue_place), _) => {
                                println!("Found assignment {:?}", stmt);
                                seeds_arg = rvalue_place;
                                if found_bump_seed {
                                    likely_bump_seed_aliases.push(*rvalue_place);
                                }
                            },
                            Rvalue::Aggregate(box AggregateKind::Array(_), elements) => {
                                println!("Found aggregate: {:?}", elements);
                                if let Operand::Move(pl) = &elements[0] {
                                    seeds_arg = pl;
                                }
                                found_bump_seed = true;
                            }
                            _ => {}
                        }
                    }
                }

            }
            match preds.get(cur_block) {
                Some(cur_preds) if !cur_preds.is_empty() => { cur_block = cur_preds[0] },
                _ => { break; }
            }

        }
        println!("Likely aliases: {:?}", likely_bump_seed_aliases);
        likely_bump_seed_aliases
    }

    // helper function
    // Given the Place search_place, check if it was defined using one of the locals in search_list
    fn is_moved_from<'tcx>(&self, _: &LateContext, body: &'tcx mir::Body<'tcx>, block: BasicBlock, mut search_place: &Place<'tcx>, search_list: &[Local]) -> bool {
        let preds = body.predecessors();
        let bbs = body.basic_blocks();
        let mut cur_block = block;
        if let Some(search_loc) = search_place.local_or_deref_local() {
            if search_list.contains(&search_loc) {
                return true;
            }
        }
        loop {
            for stmt in bbs[cur_block].statements.iter().rev() {
                match &stmt.kind {
                    StatementKind::Assign(box (assign_place, rvalue)) if assign_place.local_or_deref_local() == search_place.local_or_deref_local() => {
                        match rvalue {
                            Rvalue::Use(Operand::Copy(rvalue_place) | Operand::Move(rvalue_place)) | Rvalue::Ref(_, _, rvalue_place) => {
                                // println!("Found assignment {:?}", stmt);
                                search_place = rvalue_place;
                                if let Some(search_loc) = search_place.local_or_deref_local() {
                                    if search_list.contains(&search_loc) {
                                        return true;
                                    }
                                }
                            },
                            _ => {}
                        }
                    },
                    _ => {}
                }
            }
            match preds.get(cur_block) {
                Some(cur_preds) if !cur_preds.is_empty() => { cur_block = cur_preds[0] },
                _ => { break; }
            }
        }
        false
    }
    fn is_bump_seed_checked<'tcx>(&self, cx: &LateContext, body: &'tcx mir::Body<'tcx>, block: BasicBlock, bump_locals: Vec<Local>) -> bool {
        let preds = body.predecessors();
        let bbs = body.basic_blocks();
        let mut cur_block = block;
        loop {
            // check every statement
            if_chain! {
                if let Some(t) = &bbs[cur_block].terminator;
                if let TerminatorKind::Call { func: func_operand, args, destination: _, cleanup: _, .. } = &t.kind;
                if let mir::Operand::Constant(box func) = func_operand;
                if let TyKind::FnDef(def_id, _callee_substs) = func.literal.ty().kind();
                if match_def_path(cx, *def_id, &["core", "cmp", "PartialEq", "ne"]) || match_def_path(cx, *def_id, &["core", "cmp", "PartialEq", "eq"]);
                if let Operand::Copy(arg0_pl) | Operand::Move(arg0_pl) = args[0];
                if let Operand::Copy(arg1_pl) | Operand::Move(arg1_pl) = args[1];
                then {
                    // if either arg0 or arg1 came from one of the bump_locals, then we know
                    // this eq/ne check was operating on the bump_seed.
                    if self.is_moved_from(cx, body, cur_block, &arg0_pl, &bump_locals) || self.is_moved_from(cx, body, cur_block, &arg1_pl, &bump_locals) {
                        // we found the check. if it dominates the call to invoke, then the check
                        // is assumed to be sufficient!
                        return body.dominators().is_dominated_by(block, cur_block);
                    }
                }
            }

            match preds.get(cur_block) {
                Some(cur_preds) if !cur_preds.is_empty() => { cur_block = cur_preds[0] },
                _ => { break; }
            }
        }
        false
    }
}

#[test]
fn insecure() {
    dylint_testing::ui_test_example(env!("CARGO_PKG_NAME"), "insecure");
}

#[test]
fn secure() {
    dylint_testing::ui_test_example(env!("CARGO_PKG_NAME"), "secure");
}

#[test]
fn recommended() {
    dylint_testing::ui_test_example(env!("CARGO_PKG_NAME"), "recommended");
}
