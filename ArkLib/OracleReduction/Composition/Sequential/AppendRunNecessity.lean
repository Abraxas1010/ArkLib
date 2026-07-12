/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRun

/-! # Necessity of the Message-Opening Hypothesis for `Prover.append_run`

This file answers the converse question left open by
`Composition/Sequential/AppendRun.lean`: is the message-opening hypothesis of
`append_run_of_message_opening` (and a fortiori the challenge-freeness of
`append_run_of_challenge_free`) actually needed, or is the raw
run-factorization identity true for every pair of provers?

**It is needed.** `raw_factorization_fails` is a kernel-checked counterexample:
for the smallest protocol pair whose boundary round is a *challenge* (empty
left protocol, one `V_to_P` round on the right) and a prover whose handoff
output performs an oracle query, the composed prover's run is **not** equal to
the sequential composition of the two runs. The reason is effect *order*, not
effect *content*: the composed machine's first action is sampling the boundary
challenge (a query in the right/`Sum.inr` component of the lifted spec), while
the sequential form's first action is the handoff output's ambient oracle
query (left/`Sum.inl`). Since `OracleComp` is a free monad, the two
computations differ at their head constructor's query index, and a Boolean
head-query observer (`headIsLeft`) turns that disagreement into `False` by
kernel evaluation alone — no probabilistic or semantic argument is required.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`
(checked with `#print axioms`).
-/

namespace ArkLib.AppendRunNecessity

open ProtocolSpec OracleSpec OracleComp

-- Minimal instance: empty left protocol, one V-round right protocol,
-- one Bool-oracle ambient spec, an output that queries it.
def oS : OracleSpec Unit := Unit →ₒ Bool
def pS1 : ProtocolSpec 0 := ⟨![], ![]⟩
def pS2 : ProtocolSpec 1 := ⟨![.V_to_P], ![Bool]⟩

def P1 : Prover oS Unit Unit Unit Unit pS1 where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => absurd i.1.isLt (by simp)
  receiveChallenge := fun i => absurd i.1.isLt (by simp)
  output := fun _ => do let _ ← (query (spec := oS) () : OracleComp oS Bool); pure ((), ())

def P2 : Prover oS Unit Unit Unit Unit pS2 where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => absurd i.2 (by fin_cases i)
  receiveChallenge := fun _ _ => pure (fun _ => ())
  output := fun _ => pure ((), ())

/-- Head-query observer: `true` iff the computation's first action is a query
to the LEFT (ambient) component of a sum spec. Constructor-level: no rewriting
of lifted-query spellings needed — `congrArg headIsLeft` + kernel evaluation
discriminates the two effect orders. -/
def headIsLeft {ι₁ ι₂ : Type} {spec : OracleSpec (ι₁ ⊕ ι₂)} {α : Type} :
    OracleComp spec α → Bool
  | PFunctor.FreeM.roll (Sum.inl _) _ => true
  | _ => false

/-- **THE NECESSITY ANTIBODY**: for this challenge-opening right protocol with
an effectful handoff, raw run-factorization is FALSE — the hypothesis of
`append_run_of_message_opening` is not removable. -/
theorem raw_factorization_fails :
    ¬ ((P1.append P2).run () () = (do
      let r₁ ← liftComp (P1.run () ()) (oS + [(pS1 ++ₚ pS2).Challenge]ₒ)
      let r₂ ← liftComp (P2.run r₁.2.1 r₁.2.2) (oS + [(pS1 ++ₚ pS2).Challenge]ₒ)
      pure (r₁.1 ++ₜ r₂.1, r₂.2))) := by
  intro h
  -- Kernel evaluation: the composed run's first action is the boundary
  -- challenge query (right/`Sum.inr` component); the sequential form's first
  -- action is the handoff output's ambient query (left/`Sum.inl`). The
  -- head-query observer maps them to `false` and `true` respectively.
  exact Bool.noConfusion (congrArg headIsLeft h)

/-- Effect-order witnesses, pinned as `rfl` probes: the composed machine's
first action is the boundary challenge (right component)... -/
example : headIsLeft ((P1.append P2).run () ()) = false := rfl

/-- ...while the sequential factorization's first action is the handoff
output's ambient oracle query (left component). -/
example : headIsLeft (do
    let r₁ ← liftComp (P1.run () ()) (oS + [(pS1 ++ₚ pS2).Challenge]ₒ)
    let r₂ ← liftComp (P2.run r₁.2.1 r₁.2.2) (oS + [(pS1 ++ₚ pS2).Challenge]ₒ)
    pure (r₁.1 ++ₜ r₂.1, r₂.2)) = true := rfl

end ArkLib.AppendRunNecessity
