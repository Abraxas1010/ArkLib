# Session worklog: SeqCompose sorry-clearance (2026-07-11 evening)

CONTEXT: CompPoly #267 merged (program's first upstream merge). The living
report (~/Documents/personal/verified_zkevm_program_2026) names the next unit:
repair upstream Transcript.fst/.snd splitters, which gate the challenge-free
general append_run assembly.

DONE (this session, in this checkout on work/append-integration):
- ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean: ALL 6 sorries removed.
  * append_Type_castAdd / append_Type_natAdd (new transport lemmas)
  * Transcript.fst / Transcript.snd — uniform cast-based definitions
  * FullTranscript.rtake_append_right — HEq dissolve (eqRec_heq/cast_heq)
  * seqComposeChallengeEquiv.left_inv + seqComposeMessageEquiv.left_inv —
    rw! (castMode := .all) [Fin.splitSum_embedSum] + rfl
- Probe files: scratch_transcript_splitters.lean, scratch_rtake_probe.lean,
  scratch_equiv_probe.lean (all compile clean)
- scratch_append_run_phase1.lean: Brick 0 (take_append_of_le) DRAFTED, not
  yet compiled (waiting on full lake build ArkLib verification run).
- PR body drafted: scratchpad pr_body_seqcompose.md

NEXT (in order):
1. Full `lake build ArkLib` green → cherry-pick SeqCompose fix onto new branch
   from origin/main → push to fork → open PR (title:
   "fix(ProtocolSpec): prove the partial-transcript splitters and index
   equivalences for sequential composition (6 sorries removed)")
2. Compile Brick 0; then phase-1 left-region runToRound invariant
   (Fin.induction, field lemmas from scratch_append_general.lean).
3. Update heyting-imm ledger + paper appendix (repair no longer "gated on
   others" — it is now OUR submitted PR).

TRAPS:
- rw with mk-index lemmas → motive failure; use `show` when the index bridge
  is rfl (proof irrelevance), conv_lhs otherwise.
- rw! does NOT auto-close with rfl; add explicit rfl after.
- `set`+`clear_value`+`subst` fails to abstract under implicit-arg eta
  mismatch; rw! (castMode := .all) is the reliable dependent-pair rewriter.
- Elaborator solves implicit pSpec₁ against take-form goals; pin BOTH
  (pSpec₁ := ..) (pSpec₂ := ..) in cast lemma applications inside definitions.

## UPDATE (same session, late evening): PHASE 1 PROVEN
- ArkLib PR #641 OPENED (fix/seqcompose-transcript-splitters → Verified-zkEVM/ArkLib
  main): all 6 SeqCompose.lean sorries removed; full lake build ArkLib green (4048 jobs).
- scratch_append_general.lean EXTENDED and fully compiling, 0 sorries:
  B0/B1/B1'/B2/B3/B4/B5/B6/B7 bricks + THE PHASE-1 INVARIANT
  `append_runToRound_left_of_challenge_free` (challenge-free left-region
  runToRound at abstract indices). #print axioms: house trio.
- NEW TRAPS BANKED:
  * The two-hop MonadLiftT instance (oSpec→sum₁→sum_app) is NOT syntactically
    the one-hop (oSpec→sum_app); pin B4's RHS to `liftComp` — liftComp_eq_liftM
    is rfl at the one-hop route, so congr 1 closes the sources by itself.
  * `simp only []` proj-reduces (pair).1/.2 of literal pairs — needed before
    rw with cast-pattern lemmas.
  * cast-composition collapse across defeq-but-differently-spelled index types:
    avoid cast_cast (pattern won't match); use
    eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)).
  * Keep congrArg₂ Prod h₁ h₂ INLINE (not behind a `have hprod`) so
    cast_prod_fst/snd patterns can match the congrArg₂ head.
  * bind_congr `apply` gets stuck on Bind ?m — use congr 1 + funext, with
    proof-irrelevant source mismatches closed automatically or by rfl.
- REMAINING (next session): boundary round m handoff at runToRound level,
  right-region invariant, assembly to challenge-free Prover.append_run.

## SESSION 2026-07-12: THE CHALLENGE-FREE append_run IS PROVEN
- scratch_append_general.lean: 0 errors (grep -cE "error"), all three top
  theorems at house axiom trio (#print axioms verified):
  * append_runToRound_right_of_challenge_free (boundary G-L3 base + R7 step)
  * append_run_of_challenge_free (THE ASSEMBLY — upstream Append.lean:360
    sorry, challenge-free instance, arity m ≥ 0 × n ≥ 1)
- Non-vacuity verified: assembly statement NOT closed by rfl.
- NEW BRICKS: vappend_take, take_append_add (right-prefix spec identity),
  trGlue (= happend transported along it) + concat/zero/full laws,
  PrvState_right (décalage via Fin.append_right route), R7 (G-L4 at the
  reducing jv+1 spelling), A0 liftComp_prover_run, B4'/R6' liftComp mirrors.
- METHODOLOGY BANKED (the decisive tricks):
  * Pin ALL indices at `jv+1` (second-arg successor reduces definitionally;
    `1+jv` and `m+1+jv` never do) — kills every add-assoc defeq wall.
  * Replace rw/erw with Eq.trans + congrArg TERM-SPLICES when instance or
    index spellings defeat matching — unification is fully defeq-tolerant.
  * Free-monad pure_bind is DEFINITIONAL; liftComp_pure is rfl; cast along
    proof-irrelevant-equal types is definitionally the identity (so
    trGlue_full closes by rfl).
  * Ambient instance search picks the TWO-HOP MonadLiftT inside lambdas;
    spell liftComp in congrArg functions.
  * Hoist `by omega` holes into named `have`s before congrArg-splices
    (synthetic-opaque metas block defeq unification).
  * `include P₁ P₂ in` for section-var access in derivation bodies.
- CRITICAL TOOLING TRAP (nearly shipped a false claim):
  grep "error:" MISSES Lean 4.30's `error(lean.kind):` diagnostics, and
  recovery-elaboration injects sorryAx with NO sorry-warning. Trust ONLY
  `grep -cE "error"` = 0 plus `#print axioms`.
- REMAINING: n=0 degenerate case; liftM-ambient bridging for the upstream
  statement spelling; upstream PR of the assembly; general challenge-lift
  alignment (research-grade, unchanged).

## SESSION 2026-07-12 (closure phase): ALL THREE VACANCIES FILLED → PR #643
- (a) n=0 case PROVEN: Z1 append_output_zero + append_run_of_challenge_free_zero
  (hCF₂ vacuous over Fin 0 — only hCF₁ needed). Endgame insight: at n=0 the
  glue laws COMPOSE — trLeft (last m) T ≡ T ++ₜ default is definitional
  (both proof-irrelevant casts of T), so congr 1 closes the final mile.
- (b) liftM-spelling bridge: append_run_of_challenge_free_liftM — the EXACT
  upstream do-block (destructuring lets + ambient liftM) := the main theorem
  BY DEFEQ (ambient route resolves one-hop; destructuring = projections by
  structure eta).
- (c) UPSTREAM PR #643 OPENED: module
  ArkLib/OracleReduction/Composition/Sequential/AppendRun.lean (registered in
  ArkLib.lean), full lake build ArkLib green (4049 jobs), commit 6936c0b on
  feat/append-run-challenge-free (stacked on #631+#633+#641 content).
- Invocation-2 audit: n=0 non-vacuity verified (rfl fails); hCF₁ load-bearing
  (9 uses); axiom trio on both new theorems (#print axioms); original upstream
  sorry intentionally left for the general case (stated in PR body).
- CANONICAL COPY: the module on feat/append-run-challenge-free; the scratch
  on work/append-integration remains the dev surface (now divergent).
- NEW TRAP: opaque-head bind-assoc is NOT definitional in FreeM — nested
  do-blocks over unreduced liftComp heads need bind_assoc as a term-leg even
  when everything else in the chain is defeq.
