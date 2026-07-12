/- Fill the two sorried SubSpec instances in Composition/Sequential/Append.lean:
   the challenge-oracle spec of each component protocol embeds into the challenge
   oracle spec of the appended protocol. Lens data: `ChallengeIdx.inl/.inr` on
   indices, transport along the Challenge-type equality on responses. -/

import ArkLib.OracleReduction.Composition.Sequential.Append

open ProtocolSpec OracleSpec OracleComp

namespace SubSpecScratch

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The challenge type at a left-embedded index of the appended protocol is the
left protocol's challenge type. -/
theorem Challenge_inl (i : pSpec₁.ChallengeIdx) :
    (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i := by
  simp only [ProtocolSpec.append, Challenge, ChallengeIdx.inl, Fin.vappend_eq_append,
    Fin.append_left]

/-- The challenge type at a right-embedded index of the appended protocol is the
right protocol's challenge type. -/
theorem Challenge_inr (i : pSpec₂.ChallengeIdx) :
    (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i := by
  simp only [ProtocolSpec.append, Challenge, ChallengeIdx.inr, Fin.vappend_eq_append,
    Fin.append_right]

instance : [pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift q := ⟨⟨ChallengeIdx.inl q.input.1, q.input.2⟩,
    q.cont ∘ fun r => cast (Challenge_inl q.input.1) r⟩
  onQuery t := ⟨ChallengeIdx.inl t.1, t.2⟩
  onResponse t r := cast (Challenge_inl t.1) r

instance : [pSpec₂.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift q := ⟨⟨ChallengeIdx.inr q.input.1, q.input.2⟩,
    q.cont ∘ fun r => cast (Challenge_inr q.input.1) r⟩
  onQuery t := ⟨ChallengeIdx.inr t.1, t.2⟩
  onResponse t r := cast (Challenge_inr t.1) r

end SubSpecScratch
