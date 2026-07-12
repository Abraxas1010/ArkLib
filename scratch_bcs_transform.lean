/- T1.S2 scratch (NOT for PR): the BCS transform constructions, stage 1
   (commit-then-reveal over direct openings), per the design posted on ArkLib #627.

   Architecture (all in their idiom, composing with `Reduction.append` at T1.S3):
   * phase 1, over `pSpec.bcsCompile Com` (= `renameMessage`): the COMMITTING PROVER
     wraps the original prover — each oracle message is committed in-round, the
     (message, decommitment, commitment) triple retained in state; challenges are
     retained too; the COLLECT VERIFIER packages transcript commitments + challenges
     into the mid statement.
   * phase 2, a single reveal message: the prover reveals its (message, decommitment)
     map; the CHECK-THEN-REPLAY VERIFIER verifies every opening against the carried
     commitments, rebuilds the ORIGINAL transcript from revealed messages + carried
     challenges, and replays the original verifier on it.

   Stage-1 restrictions (as recorded on #627): direct openings (an abstract
   per-message `DirectCommit` with a boolean `verifyOpen`; the ArkLib
   `Commitment.Scheme` wiring and the Merkle instantiation follow), plain
   `Reduction` (oracle-statement outputs deferred with the `Sum.inl` embed
   restriction), reveal-all (selective opening is stage 2).

   Mid-statement uses `Option`-maps so the honest prover's output agrees with the
   collect verifier's by construction; totality holds at completeness time. -/

import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.BCS.Basic

namespace BcsScratch

open ProtocolSpec OracleSpec OracleComp

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- Stage-1 abstract direct-opening commitment: commit inside `OracleComp oSpec`,
verify an opening purely. (`Commitment.Scheme` instantiation follows in T1.S5.) -/
structure DirectCommit (oSpec : OracleSpec ι) (M C Dc : Type) where
  commit : M → OracleComp oSpec (C × Dc)
  verifyOpen : C → M → Dc → Bool

/-- The compiled first-phase protocol: message types replaced by commitment types. -/
@[reducible]
def bcsCompile (pSpec : ProtocolSpec n) (Com : pSpec.MessageIdx → Type) : ProtocolSpec n :=
  pSpec.renameMessage Com

/-- Message indices are unchanged by compilation (directions are preserved). -/
@[simp]
lemma bcsCompile_MessageIdx (Com : pSpec.MessageIdx → Type) :
    (bcsCompile pSpec Com).MessageIdx = pSpec.MessageIdx := rfl

/-- Compiled message types are the commitment types. -/
@[simp]
lemma bcsCompile_Message (Com : pSpec.MessageIdx → Type) (i : pSpec.MessageIdx) :
    (bcsCompile pSpec Com).Message i = Com i := by
  simp [bcsCompile, renameMessage, Message, i.2]

/-- Compiled challenge types are the original ones. -/
@[simp]
lemma bcsCompile_Challenge (Com : pSpec.MessageIdx → Type) (i : pSpec.ChallengeIdx) :
    (bcsCompile pSpec Com).Challenge i = pSpec.Challenge i := by
  have hdir : pSpec.dir i.1 ≠ Direction.P_to_V := by
    have := i.2; intro hcontra; rw [hcontra] at this; exact Direction.noConfusion this
  simp [bcsCompile, renameMessage, Challenge, hdir]

section Data

variable (pSpec) (Com : pSpec.MessageIdx → Type) (D : pSpec.MessageIdx → Type)

/-- What the prover retains per committed message. -/
@[reducible]
def Retained (i : pSpec.MessageIdx) : Type := pSpec.Message i × D i × Com i

/-- The reveal payload: per-message (message, decommitment); `Option` because it is
also the prover's in-flight accumulator. -/
@[reducible]
def RevealMap : Type := ∀ i : pSpec.MessageIdx, Option (pSpec.Message i × D i)

/-- The compiled mid statement: input statement + per-message commitments +
challenges (Option-maps so the honest prover can reproduce it from its state). -/
@[reducible]
def StmtMid (StmtIn : Type) : Type :=
  StmtIn × (∀ i : pSpec.MessageIdx, Option (Com i)) ×
    (∀ i : pSpec.ChallengeIdx, Option (pSpec.Challenge i))

end Data

/-! ## Phase 1: the committing prover and the collect verifier -/

section Phase1

variable (Com : pSpec.MessageIdx → Type) (D : pSpec.MessageIdx → Type)
  (schemes : ∀ i : pSpec.MessageIdx, DirectCommit oSpec (pSpec.Message i) (Com i) (D i))

/-- Insert into a dependent `Option`-map at index `i`. -/
def mapInsert {α : pSpec.MessageIdx → Type}
    (m : ∀ j : pSpec.MessageIdx, Option (α j)) (i : pSpec.MessageIdx) (v : α i) :
    ∀ j : pSpec.MessageIdx, Option (α j) :=
  fun j => if h : j = i then some (h ▸ v) else m j

def chalInsert {α : pSpec.ChallengeIdx → Type}
    (m : ∀ j : pSpec.ChallengeIdx, Option (α j)) (i : pSpec.ChallengeIdx) (v : α i) :
    ∀ j : pSpec.ChallengeIdx, Option (α j) :=
  fun j => if h : j = i then some (h ▸ v) else m j

/-- The committing prover: wraps `P`, committing each oracle message in-round and
retaining `(message, decommitment, commitment)` plus every challenge; outputs the
mid statement (from its own records) and the enriched witness. -/
def committingProver (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prover oSpec StmtIn WitIn
      (StmtMid pSpec Com StmtIn) ((StmtOut × WitOut) × RevealMap pSpec D)
      (bcsCompile pSpec Com) where
  PrvState := fun i => StmtIn × P.PrvState i ×
    (∀ j : pSpec.MessageIdx, Option (Retained pSpec Com D j)) ×
    (∀ j : pSpec.ChallengeIdx, Option (pSpec.Challenge j))
  input := fun ctx => (ctx.1, P.input ctx, fun _ => none, fun _ => none)
  sendMessage := fun i st => do
    let (m, st') ← P.sendMessage i st.2.1
    let (cm, d) ← (schemes i).commit m
    return ((bcsCompile_Message Com i) ▸ cm,
      (st.1, st', mapInsert (pSpec := pSpec) st.2.2.1 i (m, d, cm), st.2.2.2))
  receiveChallenge := fun i st => do
    let f ← P.receiveChallenge i st.2.1
    return fun c =>
      let c' : pSpec.Challenge i := (bcsCompile_Challenge Com i) ▸ c
      (st.1, f c', st.2.2.1, chalInsert (pSpec := pSpec) st.2.2.2 i c')
  output := fun st => do
    let (stmtOut, witOut) ← P.output st.2.1
    return ((st.1, fun j => (st.2.2.1 j).map (·.2.2), st.2.2.2),
      ((stmtOut, witOut), fun j => (st.2.2.1 j).map (fun r => (r.1, r.2.1))))

/-- The collect verifier: package the compiled transcript's commitments and
challenges (as `some`s) with the input statement. Pure. -/
def collectVerifier :
    Verifier oSpec StmtIn (StmtMid pSpec Com StmtIn) (bcsCompile pSpec Com) where
  verify := fun stmt tr => pure
    (stmt,
     fun j => some ((bcsCompile_Message Com j) ▸ tr.messages j),
     fun j => some ((bcsCompile_Challenge Com j) ▸ tr.challenges j))

end Phase1

/-! ## Phase 2: the reveal message and the check-then-replay verifier -/

section Phase2

variable (Com : pSpec.MessageIdx → Type) (D : pSpec.MessageIdx → Type)
  (schemes : ∀ i : pSpec.MessageIdx, DirectCommit oSpec (pSpec.Message i) (Com i) (D i))

/-- The reveal round: a single P→V message carrying the reveal map. -/
@[reducible, simp]
def revealSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[RevealMap pSpec D]⟩

/-- The reveal prover: sends its retained (message, decommitment) map; outputs the
original prover's own output statement/witness (threaded through the mid witness). -/
def revealProver :
    Prover oSpec (StmtMid pSpec Com StmtIn) ((StmtOut × WitOut) × RevealMap pSpec D)
      StmtOut WitOut (revealSpec (pSpec := pSpec) D) where
  PrvState
  | 0 => (StmtOut × WitOut) × RevealMap pSpec D
  | 1 => StmtOut × WitOut
  input := fun ctx => ctx.2
  sendMessage | ⟨0, _⟩ => fun st => pure (st.2, st.1)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => pure st

/-- Materialize a total dependent map from an `Option`-map over a fintype index,
failing (constructively decidably) if any entry is missing. -/
def totalize {κ : Type} [Fintype κ] [DecidableEq κ] {α : κ → Type}
    (f : ∀ j : κ, Option (α j)) : Option (∀ j : κ, α j) :=
  if h : ∀ j, (f j).isSome then some (fun j => (f j).get (h j)) else none

/-- Rebuild the ORIGINAL transcript from revealed messages + carried challenges.
Named (rather than inlined in the verifier) so the completeness relation can cite
the exact transcript the replay runs on. -/
def rebuildTranscript (opens : ∀ j : pSpec.MessageIdx, pSpec.Message j × D j)
    (chals : ∀ j : pSpec.ChallengeIdx, pSpec.Challenge j) : FullTranscript pSpec :=
  fun i =>
    match h : pSpec.dir i with
    | .P_to_V => (opens ⟨i, h⟩).1
    | .V_to_P => chals ⟨i, h⟩

/-- The check-then-replay verifier: totalize commitments/challenges/reveals, verify
every opening, rebuild the ORIGINAL transcript from revealed messages + carried
challenges, and replay the original verifier on it. Refuses (`OptionT` failure) on
any missing datum or failed opening. -/
def checkReplayVerifier [DecidableEq ι]
    (origV : Verifier oSpec StmtIn StmtOut pSpec) :
    Verifier oSpec (StmtMid pSpec Com StmtIn) StmtOut (revealSpec (pSpec := pSpec) D) where
  verify := fun stmt tr => do
    let reveal : RevealMap pSpec D := tr 0
    let some coms := totalize stmt.2.1 | failure
    let some chals := totalize stmt.2.2 | failure
    let some opens := totalize reveal | failure
    guard (∀ j : pSpec.MessageIdx, (schemes j).verifyOpen (coms j) (opens j).1 (opens j).2)
    origV.verify stmt.1 (rebuildTranscript (pSpec := pSpec) D opens chals)

/-- The reveal-round reduction on its own (phase 2 of the compiled protocol). -/
def revealReduction [DecidableEq ι] (origV : Verifier oSpec StmtIn StmtOut pSpec) :
    Reduction oSpec (StmtMid pSpec Com StmtIn) ((StmtOut × WitOut) × RevealMap pSpec D)
      StmtOut WitOut (revealSpec (pSpec := pSpec) D) :=
  ⟨revealProver Com D, checkReplayVerifier Com D schemes origV⟩

end Phase2

/-! ## Phase 2 completeness -/

section Phase2Completeness

variable [DecidableEq ι]
  (Com : pSpec.MessageIdx → Type) (D : pSpec.MessageIdx → Type)
  (schemes : ∀ i : pSpec.MessageIdx, DirectCommit oSpec (pSpec.Message i) (Com i) (D i))
  (origV : Verifier oSpec StmtIn StmtOut pSpec)

/-- The honest-reveal input relation for phase 2: all three `Option`-maps are total,
every opening verifies, and the original verifier — replayed on the rebuilt
transcript — deterministically returns exactly the statement the prover carries,
which is `relOut`-related to the carried witness. Phase-1 completeness will show the
honest committing prover + collect verifier land in this relation. -/
def revealRelIn (relOut : Set (StmtOut × WitOut)) :
    Set ((StmtMid pSpec Com StmtIn) × ((StmtOut × WitOut) × RevealMap pSpec D)) :=
  { p | ∃ coms chals opens,
      totalize p.1.2.1 = some coms ∧
      totalize p.1.2.2 = some chals ∧
      totalize p.2.2 = some opens ∧
      (∀ j : pSpec.MessageIdx, (schemes j).verifyOpen (coms j) (opens j).1 (opens j).2) ∧
      origV.verify p.1.1 (rebuildTranscript (pSpec := pSpec) D opens chals) = pure p.2.1.1 ∧
      p.2.1 ∈ relOut }

variable {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp)) (relOut : Set (StmtOut × WitOut))

/-- **Phase-2 (reveal round) perfect completeness**: an honest reveal — total maps,
verifying openings, replay agreeing with the carried output — always accepts, with
the verifier's output equal to the prover's. The SendWitness recipe applies: the
prover leg of `Reduction.run` collapses definitionally (`default` at literal
index 0); the verifier leg reduces to `pure` by rewriting the three totalizations,
discharging the guard, and replaying the determinism hypothesis. -/
theorem revealReduction_completeness :
    (revealReduction Com D schemes origV).perfectCompleteness init impl
      (revealRelIn Com D schemes origV relOut) relOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  obtain ⟨coms, chals, opens, hc, hch, ho, hver, hrep, hOut⟩ := hIn
  -- The verifier leg reduces to `pure` under the honest hypotheses.
  have hverify : (revealReduction (StmtIn := StmtIn) (StmtOut := StmtOut) (WitOut := WitOut)
      Com D schemes origV).verifier.verify stmtIn
      (ProtocolSpec.Transcript.concat (m := 0) witIn.2
        (default : (revealSpec (pSpec := pSpec) D).Transcript 0)) = pure witIn.1.1 := by
    show (do
      let some coms := totalize stmtIn.2.1 | failure
      let some chals := totalize stmtIn.2.2 | failure
      let some opens := totalize witIn.2 | failure
      guard (∀ j : pSpec.MessageIdx, (schemes j).verifyOpen (coms j) (opens j).1 (opens j).2)
      origV.verify stmtIn.1 (rebuildTranscript (pSpec := pSpec) D opens chals)) = pure witIn.1.1
    rw [hc, hch, ho]
    simp only [guard, if_pos hver, hrep, pure_bind]
  -- The prover leg collapses definitionally (the SendWitness recipe: `default` at
  -- literal index 0).
  have hpro : (revealReduction Com D schemes origV).prover.run stmtIn witIn =
      (pure (ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1) :
        OracleComp _ _) := rfl
  -- The whole run is then a `pure` value.
  have hrun : ((revealReduction Com D schemes origV).run stmtIn witIn).run =
      (pure (some ((ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1),
        witIn.1.1)) : OracleComp _ _) := by
    unfold Reduction.run
    simp only [OptionT.run_bind, hpro, Option.elimM, Verifier.run]
    change (pure (some (ProtocolSpec.Transcript.concat (m := 0) witIn.2
        (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1)) :
      OracleComp _ _) >>= _ = _
    rw [pure_bind]
    change OptionT.run (liftM
      ((revealReduction (StmtIn := StmtIn) (StmtOut := StmtOut) (WitOut := WitOut)
        Com D schemes origV).verifier.verify stmtIn
        (ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0))).run) >>= _ = _
    rw [hverify]
    rfl
  simp only [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ support (StateT.run' (simulateQ _
      (pure (some ((ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1),
        witIn.1.1)) : OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ support (Prod.fst <$>
      (pure (some ((ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1),
        witIn.1.1)) : StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp only [map_pure, support_pure]
    exact fun h => Option.some_ne_none _ (Set.mem_singleton_iff.mp h).symm
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support (StateT.run' (simulateQ _
      (pure (some ((ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1),
        witIn.1.1)) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support (Prod.fst <$>
      (pure (some ((ProtocolSpec.Transcript.concat (m := 0) witIn.2
          (default : (revealSpec (pSpec := pSpec) D).Transcript 0), witIn.1),
        witIn.1.1)) : StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨hOut, rfl⟩

end Phase2Completeness

/-! ## The compiled reduction: phase 1 ++ phase 2 -/

section Compose

variable (Com : pSpec.MessageIdx → Type) (D : pSpec.MessageIdx → Type)
  (schemes : ∀ i : pSpec.MessageIdx, DirectCommit oSpec (pSpec.Message i) (Com i) (D i))

/-- **The BCS-compiled reduction (stage 1, commit-then-reveal)**: the committing
prover + collect verifier over `bcsCompile pSpec Com`, appended with the reveal
round and the check-then-replay verifier. -/
def bcsReduction [DecidableEq ι]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut
      ((bcsCompile pSpec Com) ++ₚ (revealSpec (pSpec := pSpec) D)) :=
  Reduction.append
    ⟨committingProver Com D schemes R.prover, collectVerifier Com⟩
    ⟨revealProver Com D, checkReplayVerifier Com D schemes R.verifier⟩

end Compose

end BcsScratch
