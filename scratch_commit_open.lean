/- T1 stage-1 vertical slice (NOT for PR yet): the 2-round COMMIT-AND-OPEN protocol
   — the BCS compilation of `SendWitness` — with an *effectful* commitment, and its
   end-to-end perfect completeness.

   Why direct (not through `Reduction.append`): the upstream Append security layer
   is currently open (19 `sorry`s incl. `Prover.append_run`, `append_completeness`,
   with a TODO asking for the right side conditions). At concrete sizes the composed
   protocol is just a 2-round protocol, so we state it directly; the definitional
   tie to `bcsReduction`-of-`SendWitness` is deferred until the append run lemmas
   exist upstream.

   Content beyond the SendWitness/phase-2 recipes: the prover is NOT pure — round 0
   binds an abstract `commit : OracleComp oSpec (C × D)`. The run characterization
   is "pure modulo one effectful bind head" (`prover_run_raw`, still `rfl`! — the
   lift wraps the whole sendMessage body, so the stuck head is
   `liftM (commit >>= pure-continuation)`), and completeness needs
   support/probFailure reasoning through that bind. -/

import ArkLib.ProofSystem.Component.SendWitness

open ProtocolSpec OracleSpec OracleComp

namespace CommitOpen

variable {ι : Type} {oSpec : OracleSpec ι} {Statement Witness C D : Type}

/-- Abstract direct-opening commitment (as in the BCS stage-1 design on #627):
commit inside `OracleComp oSpec` (covers hash/random-oracle commitments), verify an
opening purely. -/
structure DirectCommit (oSpec : OracleSpec ι) (M C D : Type) where
  commit : M → OracleComp oSpec (C × D)
  verifyOpen : C → M → D → Bool

/-- Two P→V rounds: the commitment, then the (message, decommitment) reveal. -/
@[reducible, simp]
def pSpec (C RM : Type) : ProtocolSpec 2 := ⟨!v[.P_to_V, .P_to_V], !v[C, RM]⟩

instance {C RM : Type} : ∀ i, VCVCompatible ((pSpec C RM).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, h⟩ => nomatch h

instance {C RM : Type} : ∀ i, SampleableType ((pSpec C RM).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, h⟩ => nomatch h

/- Pin the challenge oracle-interface family at this (reducible) `pSpec`: the
generic `challengeOracleInterface` does not match once `Challenge` unfolds. -/
instance {C RM : Type} : ∀ i, OracleInterface ((pSpec C RM).Challenge i) :=
  fun i => ProtocolSpec.challengeOracleInterface i

variable (oSpec Statement Witness)

/-- The commit-and-open prover: commit to the witness in round 0 (retaining the
decommitment), reveal in round 1. -/
@[inline, specialize]
def prover (scheme : DirectCommit oSpec Witness C D) :
    Prover oSpec Statement Witness (Statement × Witness) Unit (pSpec C (Witness × D)) where
  PrvState
  | 0 => Statement × Witness
  | 1 => Statement × Witness × D
  | 2 => Statement × Witness
  input := id
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => do
      let (c, d) ← scheme.commit wit
      pure (c, (stmt, wit, d))
  | ⟨1, _⟩ => fun ⟨stmt, wit, d⟩ => pure ((wit, d), (stmt, wit))
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ => pure ((stmt, wit), ())

/-- The commit-and-open verifier: check the opening against the commitment, output
the revealed message (mirroring `SendWitness.verifier`). -/
@[inline, specialize]
def verifier (scheme : DirectCommit oSpec Witness C D) :
    Verifier oSpec Statement (Statement × Witness) (pSpec C (Witness × D)) where
  verify := fun stmt tr => do
    guard (scheme.verifyOpen (tr 0) (tr 1).1 (tr 1).2)
    pure (stmt, (tr 1).1)

@[inline, specialize]
def reduction (scheme : DirectCommit oSpec Witness C D) :
    Reduction oSpec Statement Witness (Statement × Witness) Unit (pSpec C (Witness × D)) where
  prover := prover oSpec Statement Witness scheme
  verifier := verifier oSpec Statement Witness scheme

variable {oSpec Statement Witness}

/-- The honest transcript for witness `w`, commitment `cd.1`, decommitment `cd.2`. -/
@[reducible]
def honestTr (w : Witness) (cd : C × D) : FullTranscript (pSpec C (Witness × D)) :=
  ProtocolSpec.Transcript.concat (m := 1)
    (w, cd.2)
    (ProtocolSpec.Transcript.concat (m := 0) cd.1
      (default : (pSpec C (Witness × D)).Transcript 0))

/-- The prover's round-0 computation: commit, retain the decommitment. -/
@[reducible]
def commitStep (scheme : DirectCommit oSpec Witness C D)
    (stmtIn : Statement) (witIn : Witness) :
    OracleComp oSpec (C × Statement × Witness × D) :=
  scheme.commit witIn >>= fun x => pure (x.1, (stmtIn, witIn, x.2))

/-- **Raw prover-run characterization, definitionally**: the literal-index
`Fin.induction` collapse leaves the lifted round-0 computation as the single
effectful head; rounds 1 and output are pure. Structure eta turns the
match-lambdas into projection form, so this is `rfl`. -/
theorem prover_run_raw (scheme : DirectCommit oSpec Witness C D)
    (stmtIn : Statement) (witIn : Witness) :
    (prover oSpec Statement Witness scheme).run stmtIn witIn =
      ((((liftM (commitStep scheme stmtIn witIn) >>= fun y =>
        pure (ProtocolSpec.Transcript.concat (m := 0) y.1
          (default : (pSpec C (Witness × D)).Transcript 0), y.2)) >>= fun z =>
        pure (ProtocolSpec.Transcript.concat (m := 1) (z.2.2.1, z.2.2.2) z.1,
          (z.2.1, z.2.2.1))) >>= fun r =>
        pure (r.1, ((r.2.1, r.2.2), ()))) : OracleComp _ _) := rfl

/-- Bind-normal form of the prover run. -/
theorem prover_run (scheme : DirectCommit oSpec Witness C D)
    (stmtIn : Statement) (witIn : Witness) :
    (prover oSpec Statement Witness scheme).run stmtIn witIn =
      (liftM (commitStep scheme stmtIn witIn) >>= fun y =>
        pure (honestTr y.2.2.1 (y.1, y.2.2.2), ((y.2.1, y.2.2.1), ())) :
          OracleComp _ _) := by
  rw [prover_run_raw]
  simp only [bind_assoc, pure_bind]
  rfl

/-- The verifier at an honest transcript reduces to an opening-check `if`. -/
theorem verifier_honestTr (scheme : DirectCommit oSpec Witness C D)
    (stmtIn : Statement) (w : Witness) (cd : C × D) :
    (verifier oSpec Statement Witness scheme).verify stmtIn (honestTr w cd) =
      if scheme.verifyOpen cd.1 w cd.2 = true
      then pure (stmtIn, w) else failure := by
  show (do
    guard (scheme.verifyOpen ((honestTr w cd) 0) ((honestTr w cd) 1).1
      ((honestTr w cd) 1).2)
    pure (stmtIn, ((honestTr w cd) 1).1) : OptionT (OracleComp oSpec) _) = _
  have h0 : (honestTr (C := C) (D := D) w cd) 0 = cd.1 := rfl
  have h1 : (honestTr (C := C) (D := D) w cd) 1 = (w, cd.2) := rfl
  rw [h0, h1]
  by_cases hb : scheme.verifyOpen cd.1 w cd.2 = true
  · simp only [guard, if_pos hb, pure_bind]
  · simp only [guard, if_neg hb]
    exact failure_bind _

/-! ## End-to-end perfect completeness -/

section Completeness

variable (scheme : DirectCommit oSpec Witness C D)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (Statement × Witness))

/-- The run of the commit-and-open reduction, `Option`-valued: the lifted commit
head, then accept-or-reject by the opening check. -/
theorem reduction_run (stmtIn : Statement) (witIn : Witness) :
    ((reduction oSpec Statement Witness scheme).run stmtIn witIn).run =
      ((liftM (commitStep scheme stmtIn witIn) : OracleComp _ _) >>= fun y =>
        if scheme.verifyOpen y.1 y.2.2.1 y.2.2.2 = true
        then pure (some ((honestTr y.2.2.1 (y.1, y.2.2.2), ((y.2.1, y.2.2.1), ())),
          (stmtIn, y.2.2.1)))
        else pure none) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM]
  rw [show (reduction oSpec Statement Witness scheme).prover
    = prover oSpec Statement Witness scheme from rfl, prover_run,
    show (reduction oSpec Statement Witness scheme).verifier
    = verifier oSpec Statement Witness scheme from rfl]
  change ((liftM (commitStep scheme stmtIn witIn) >>= fun y =>
    pure (honestTr y.2.2.1 (y.1, y.2.2.2), ((y.2.1, y.2.2.1), ()))) >>= fun v =>
    pure (some v)) >>= _ = _
  simp only [bind_assoc, pure_bind, Option.elim_some]
  refine bind_congr fun y => ?_
  simp only [Verifier.run]
  rw [verifier_honestTr]
  by_cases hb : scheme.verifyOpen y.1 y.2.2.1 y.2.2.2 = true
  · rw [if_pos hb, if_pos hb]; rfl
  · rw [if_neg hb, if_neg hb]; rfl

open Classical in
/-- **End-to-end perfect completeness of commit-and-open** (the BCS compilation of
`SendWitness`): if every commitment the scheme produces verifies against its own
opening (support-level correctness — no other assumption on the commitment), then
the compiled 2-round protocol is perfectly complete for any oracle implementation.
This is the first completeness statement carried through an *effectful* prover
round in this development. -/
theorem completeness
    (hVer : ∀ w c d, (c, d) ∈ _root_.support (scheme.commit w) →
      scheme.verifyOpen c w d = true) :
    (reduction oSpec Statement Witness scheme).perfectCompleteness init impl relIn
      (Prod.fst ⁻¹' relIn) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  simp only [reduction_run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  -- Shared support fact: any simulated round-0 outcome is an honest commit outcome.
  have hy : ∀ (s : σ) (ys : (C × Statement × Witness × D) × σ),
      ys ∈ _root_.support (StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (commitStep scheme stmtIn witIn) :
          OracleComp (oSpec + [(pSpec C (Witness × D)).Challenge]ₒ) _)) s) →
      ys.1.2.1 = stmtIn ∧ ys.1.2.2.1 = witIn ∧
        scheme.verifyOpen ys.1.1 ys.1.2.2.1 ys.1.2.2.2 = true := by
    intro s ys hys
    have h1 : ys.1 ∈ _root_.support (StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (commitStep scheme stmtIn witIn) :
          OracleComp (oSpec + [(pSpec C (Witness × D)).Challenge]ₒ) _)) s) := by
      rw [StateT.run'_eq, support_map]
      exact ⟨ys, hys, rfl⟩
    have h2 := support_simulateQ_run'_subset _ _ s h1
    rw [show (liftM (commitStep scheme stmtIn witIn) :
        OracleComp (oSpec + [(pSpec C (Witness × D)).Challenge]ₒ) _)
      = liftComp (commitStep scheme stmtIn witIn) _ from rfl,
      support_liftComp] at h2
    simp only [commitStep, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at h2
    obtain ⟨cd, hcd, hys1⟩ := h2
    rw [hys1]
    exact ⟨rfl, rfl, hVer _ _ _ hcd⟩
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ h
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind] at h
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at h
    obtain ⟨p, ⟨ys, hys, hp⟩, hnone⟩ := h
    rw [if_pos (hy s ys hys).2.2] at hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp] at hnone
    exact Option.some_ne_none _ hnone
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind] at hx
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨p, ⟨ys, hys, hp⟩, hsome⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy s ys hys
    rw [if_pos hy3] at hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp] at hsome
    cases Option.some.inj hsome
    refine ⟨?_, ?_⟩
    · show (stmtIn, ys.1.2.2.1) ∈ relIn
      rw [hy2]; exact hIn
    · show (ys.1.2.1, ys.1.2.2.1) = (stmtIn, ys.1.2.2.1)
      rw [hy1]

end Completeness

/-! ## T1.S5: concrete instantiation — hash commit-and-open, zero hypotheses -/

section HashInstantiation

variable {C : Type} [DecidableEq C]

/-- The standard-model hash commitment: commit = apply a fixed function
`h : Witness → C` (e.g. a Merkle root of the witness's serialization);
decommitment is trivial; opening check recomputes. (The random-oracle variant,
where `commit` queries and hence verification must also query, needs the
oracle-verifier protocol shape and is a separate theorem.) -/
def hashCommit (h : Witness → C) : DirectCommit oSpec Witness C Unit where
  commit m := pure (h m, ())
  verifyOpen c m _ := decide (c = h m)

/-- Support-level correctness of the hash commitment — discharging
`completeness`' sole hypothesis. -/
theorem hashCommit_hVer (h : Witness → C) :
    ∀ w c d, (c, d) ∈ _root_.support ((hashCommit (oSpec := oSpec) h).commit w) →
      (hashCommit (oSpec := oSpec) h).verifyOpen c w d = true := by
  intro w c d hcd
  simp only [hashCommit, support_pure, Set.mem_singleton_iff] at hcd
  rw [show c = h w from congrArg Prod.fst hcd]
  simp [hashCommit]

/-- **Fully-instantiated end-to-end completeness, zero hypotheses**: the
hash commit-and-open protocol is perfectly complete, for any hash function,
any oracle implementation, any initial state. -/
theorem hashCommit_completeness (h : Witness → C)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (Statement × Witness)) :
    (reduction oSpec Statement Witness (hashCommit h)).perfectCompleteness
      init impl relIn (Prod.fst ⁻¹' relIn) :=
  completeness (hashCommit h) init impl relIn (hashCommit_hVer h)

end HashInstantiation


end CommitOpen
