/- T1.S3: fill SendWitness.reduction_completeness (ArkLib's open sorry). -/
import ArkLib.ProofSystem.Component.SendWitness

open ProtocolSpec OracleSpec OracleComp

namespace SwScratch

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} {Statement Witness : Type}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (Statement × Witness))

/-- THE missing upstream infrastructure: one-step unfolding of `runToRound`
(the reason component completeness proofs are stuck). -/
theorem runToRound_succ {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn WitIn StmtOut WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin n) (stmt : StmtIn) (wit : WitIn) :
    prover.runToRound i.succ stmt wit =
      prover.processRound i (prover.runToRound i.castSucc stmt wit) :=
  Fin.induction_succ _ _ _

/-- Specialization at the last round of a 1-round protocol, stated with `Fin.last 1`
so `simp` can fire without a dependent-index motive (the indices are defeq). -/
theorem runToRound_last_one {pSpec : ProtocolSpec 1}
    {StmtIn WitIn StmtOut WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    prover.runToRound (Fin.last 1) stmt wit =
      prover.processRound 0 (prover.runToRound (0 : Fin 2) stmt wit) :=
  runToRound_succ (oSpec := oSpec) prover (0 : Fin 1) stmt wit

open Classical in
theorem sendWitness_completeness :
    (SendWitness.reduction oSpec Statement Witness).perfectCompleteness init impl relIn
      (SendWitness.toRelOut relIn) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  have hrun : (SendWitness.reduction oSpec Statement Witness).run stmtIn witIn =
      pure ((Transcript.concat (m := 0) witIn
          (default : (SendWitness.pSpec Witness).Transcript 0), (stmtIn, witIn), ()),
        (stmtIn, witIn)) := rfl
  simp only [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ support (StateT.run' (simulateQ _
      (pure (some ((Transcript.concat (m := 0) witIn
          (default : (SendWitness.pSpec Witness).Transcript 0), (stmtIn, witIn), ()),
        (stmtIn, witIn))) : OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ support (Prod.fst <$>
      (pure (some ((Transcript.concat (m := 0) witIn
          (default : (SendWitness.pSpec Witness).Transcript 0), (stmtIn, witIn), ()),
        (stmtIn, witIn))) : StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp only [map_pure, support_pure]
    exact fun h => Option.some_ne_none _ (Set.mem_singleton_iff.mp h).symm
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support (StateT.run' (simulateQ _
      (pure (some ((Transcript.concat (m := 0) witIn
          (default : (SendWitness.pSpec Witness).Transcript 0), (stmtIn, witIn), ()),
        (stmtIn, witIn))) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support (Prod.fst <$>
      (pure (some ((Transcript.concat (m := 0) witIn
          (default : (SendWitness.pSpec Witness).Transcript 0), (stmtIn, witIn), ()),
        (stmtIn, witIn))) : StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨hIn, rfl⟩

end SwScratch

#print axioms SwScratch.sendWitness_completeness
#print axioms SwScratch.runToRound_succ
