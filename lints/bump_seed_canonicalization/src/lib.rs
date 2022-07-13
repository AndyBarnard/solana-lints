#![feature(rustc_private)]
#![feature(box_patterns)]
#![warn(unused_extern_crates)]

use if_chain::if_chain;
use rustc_hir::Body;
use rustc_lint::{LateContext, LateLintPass};

use rustc_middle::{
    mir,
    mir::terminator::TerminatorKind,
    mir::{AggregateKind, BasicBlock, BinOp, Local, Operand, Place, Rvalue, StatementKind},
    ty::TyKind,
};

use clippy_utils::{diagnostics::span_lint, match_def_path};
mod paths;

extern crate rustc_hir;
extern crate rustc_middle;

dylint_linting::impl_late_lint! {
    /// **What it does:**
    /// Finds uses of solana_program::pubkey::PubKey::create_program_address that do not check the bump_seed
    ///
    /// **Why is this bad?**
    /// Generally for every seed there should be a canonical address.
    ///
    /// **Known problems:**
    /// False positives, since the bump_seed check may be within some other function (does not
    /// trace through function calls)
    /// False negatives, since our analysis is not path-sensitive (the bump_seed check may not
    /// occur in all possible execution paths)
    ///
    /// **Example:*j
    ///
    /// ```rust
    /// // example code where a warning is issued
    ///
    /// ```
    /// Use instead:
    /// ```rust
    /// ```
    pub BUMP_SEED_CANONICALIZATION,
    Warn,
    "Finds calls to create_program_address that do not check the bump_seed",
    BumpSeedCanonicalization::default()
}

#[derive(Default)]
struct BumpSeedCanonicalization {}

impl<'tcx> LateLintPass<'tcx> for BumpSeedCanonicalization {
    fn check_body(&mut self, cx: &LateContext<'tcx>, body: &'tcx Body<'tcx>) {
        let hir_map = cx.tcx.hir();
        let body_did = hir_map.body_owner_def_id(body.id()).to_def_id();
        if !cx.tcx.def_kind(body_did).is_fn_like() || !cx.tcx.is_mir_available(body_did) {
            return;
        }
        let body_mir = cx.tcx.optimized_mir(body_did);
        let terminators = body_mir
            .basic_blocks()
            .iter_enumerated()
            .map(|(block_id, block)| (block_id, &block.terminator));
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
                            let likely_bump_locals: Vec<Local> = Self::find_bump_seed_for_seed_array(cx, body_mir, block_id, p).iter().map(|pl| pl.local).collect();
                            if !Self::is_bump_seed_checked(cx, body_mir, likely_bump_locals.as_ref()) {
                                span_lint(
                                    cx,
                                    BUMP_SEED_CANONICALIZATION,
                                    t.source_info.span,
                                    "Bump seed may not be constrained. If stored in an account, use anchor's #[account(seed=..., bump=...)] macro instead",
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}
#[derive(Eq, PartialEq)]
enum BackwardDataflowState {
    SeedsArray,
    FirstSeed,
    Bump,
}

impl BumpSeedCanonicalization {
    fn find_bump_seed_for_seed_array<'tcx>(
        _: &LateContext,
        body: &'tcx mir::Body<'tcx>,
        block: BasicBlock,
        mut seeds_arg: &Place<'tcx>,
    ) -> Vec<Place<'tcx>> {
        let preds = body.predecessors();
        let bbs = body.basic_blocks();
        let mut cur_block = block;
        let mut state = BackwardDataflowState::SeedsArray;
        let mut likely_bump_seed_aliases = Vec::<Place>::new();
        loop {
            // check every statement
            for stmt in bbs[cur_block].statements.iter().rev() {
                if let StatementKind::Assign(box (assign_place, rvalue)) = &stmt.kind {
                    // trace assignments so we have a list of locals that contain the bump_seed
                    if assign_place.local_or_deref_local() == seeds_arg.local_or_deref_local() {
                        // println!("match: {:?}", stmt);
                        match rvalue {
                            Rvalue::Use(
                                Operand::Copy(rvalue_place) | Operand::Move(rvalue_place),
                            )
                            | Rvalue::Ref(_, _, rvalue_place)
                            | Rvalue::Cast(
                                _,
                                Operand::Copy(rvalue_place) | Operand::Move(rvalue_place),
                                _,
                            ) => {
                                // println!("Found assignment {:?}", stmt);
                                seeds_arg = rvalue_place;
                                if state == BackwardDataflowState::Bump {
                                    likely_bump_seed_aliases.push(*rvalue_place);
                                }
                            }
                            Rvalue::Aggregate(box AggregateKind::Array(_), elements) => {
                                match state {
                                    BackwardDataflowState::SeedsArray if elements.len() > 1 => {
                                        // println!("Found aggregate: {:?}", elements);
                                        if let Operand::Move(pl) = elements.last().unwrap() {
                                            seeds_arg = pl;
                                            state = BackwardDataflowState::FirstSeed;
                                        }
                                    }
                                    BackwardDataflowState::FirstSeed if elements.len() == 1 => {
                                        // println!("Found aggregate (state 1): {:?}", elements);
                                        if let Operand::Move(pl) = &elements[0] {
                                            seeds_arg = pl;
                                            likely_bump_seed_aliases.push(*seeds_arg);
                                            state = BackwardDataflowState::Bump;
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            match preds.get(cur_block) {
                Some(cur_preds) if !cur_preds.is_empty() => cur_block = cur_preds[0],
                _ => {
                    break;
                }
            }
        }
        // println!("Likely aliases: {:?}", likely_bump_seed_aliases);
        likely_bump_seed_aliases
    }

    // helper function
    // Given the Place search_place, check if it was defined using one of the locals in search_list
    fn is_moved_from<'tcx>(
        _: &LateContext,
        body: &'tcx mir::Body<'tcx>,
        block: BasicBlock,
        mut search_place: &Place<'tcx>,
        search_list: &[Local],
    ) -> bool {
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
                    StatementKind::Assign(box (assign_place, rvalue))
                        if assign_place.local_or_deref_local()
                            == search_place.local_or_deref_local() =>
                    {
                        match rvalue {
                            Rvalue::Use(
                                Operand::Copy(rvalue_place) | Operand::Move(rvalue_place),
                            )
                            | Rvalue::Ref(_, _, rvalue_place) => {
                                // println!("Found assignment {:?}", stmt);
                                search_place = rvalue_place;
                                if let Some(search_loc) = search_place.local_or_deref_local() {
                                    if search_list.contains(&search_loc) {
                                        return true;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
            match preds.get(cur_block) {
                Some(cur_preds) if !cur_preds.is_empty() => cur_block = cur_preds[0],
                _ => {
                    break;
                }
            }
        }
        false
    }
    fn is_bump_seed_checked<'tcx>(
        cx: &LateContext,
        body: &'tcx mir::Body<'tcx>,
        bump_locals: &[Local],
    ) -> bool {
        for (block_id, block) in body.basic_blocks().iter_enumerated() {
            for stmt in &block.statements {
                if_chain! {
                    if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind;
                    if let Rvalue::BinaryOp(BinOp::Eq | BinOp::Ne, box (op0, op1)) = rvalue;
                    if let Operand::Copy(arg0_pl) | Operand::Move(arg0_pl) = op0;
                    if let Operand::Copy(arg1_pl) | Operand::Move(arg1_pl) = op1;
                    then {
                        if Self::is_moved_from(cx, body, block_id, arg0_pl, bump_locals) || Self::is_moved_from(cx, body, block_id, arg1_pl, bump_locals) {
                            // we found the check
                            return true;
                        }
                    }
                }
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
