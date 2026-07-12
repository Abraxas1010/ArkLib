/- Step 1 of the append-completeness program (the #627 side-condition analysis,
   issuecomment-4939141052): perfect completeness composes across `Reduction.append`
   GIVEN (a) pure verifiers, (b) the *prover-level simulated factorization* (the
   distributional shadow of the open `Prover.append_run`), and (c) R₂ complete
   uniformly in the initial state. This isolates the probabilistic content of
   upstream's `append_completeness` TODO from the dependent-index factorization
   mountain; the hypothesis `hfact` delimits exactly what remains.

   Why NOT a universal `R₂.run`-level factorization: the appended verifier chains
   V₁'s output statement while the appended prover chains P₁'s output statement.
   These coincide only on honest supports (event₁'s `prvStmtOut = stmtOut`), so an
   unconditional run-level factorization through `R₂.run` is false. The prover-level
   factorization is unconditional; the verifier side composes purely. -/

import ArkLib.OracleReduction.Composition.Sequential.Append

open ProtocolSpec OracleSpec OracleComp

namespace AppendCompleteness

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Run of a reduction with a pure verifier** (abstract prover): the `OptionT`
plumbing collapses onto the prover's run. Reusable for any reduction whose verifier
is a pure function of statement and transcript (their `support_run_pure_verifier`
premise pattern). -/
theorem Reduction.run_pure_verifier
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (f : Stmt₁ → FullTranscript pSpec₁ → Stmt₂)
    (hf : ∀ stmt td, R.verifier.verify stmt td =
      (pure (f stmt td) : OptionT (OracleComp oSpec) Stmt₂))
    (stmt : Stmt₁) (wit : Wit₁) :
    (R.run stmt wit).run =
      ((liftM (R.prover.run stmt wit) : OracleComp _ _) >>= fun r =>
        pure (some ((r.1, r.2), f stmt r.1))) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM]
  rw [show ((liftM (R.prover.run stmt wit) : OptionT (OracleComp _) _)).run
    = (liftM (R.prover.run stmt wit) : OracleComp _ _) >>= fun r => pure (some r) from rfl]
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]
  simp only [Option.elim_some, Verifier.run, hf]
  rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  [∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]

/-- **Perfect completeness composes across `Reduction.append`** under:
pure verifiers (`hf₁`, `hf₂`), the prover-level simulated factorization `hfact`
(the distributional shadow of `Prover.append_run` — the sole remaining upstream
obligation), and — the side condition answering the upstream TODO — R₂ complete
**uniformly in the initial state** (`h₂` quantifies over `init'`; the appended run
hands R₂ whatever state R₁'s prover left, so a fixed-`init` premise cannot apply). -/
theorem append_perfectCompleteness_of_proverFactorization
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (f₁ : Stmt₁ → FullTranscript pSpec₁ → Stmt₂)
    (f₂ : Stmt₂ → FullTranscript pSpec₂ → Stmt₃)
    (hf₁ : ∀ stmt td, R₁.verifier.verify stmt td =
      (pure (f₁ stmt td) : OptionT (OracleComp oSpec) Stmt₂))
    (hf₂ : ∀ stmt td, R₂.verifier.verify stmt td =
      (pure (f₂ stmt td) : OptionT (OracleComp oSpec) Stmt₃))
    (hfact : ∀ (stmt : Stmt₁) (wit : Wit₁) (s : σ),
      StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM ((R₁.append R₂).prover.run stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) s =
      (do
        let (r₁, s₁) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl _ (StateT σ ProbComp))
          (liftM (R₁.prover.run stmt wit) :
            OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s
        let (r₂, s₂) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl _ (StateT σ ProbComp))
          (liftM (R₂.prover.run r₁.2.1 r₁.2.2) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)) s₁
        pure ((r₁.1 ++ₜ r₂.1, r₂.2), s₂)))
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ init' : ProbComp σ, R₂.perfectCompleteness init' impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    ENNReal.coe_zero, tsub_zero] at h₁ h₂ ⊢
  intro stmtIn witIn hIn
  -- The appended verifier of pure verifiers is the pure composite.
  have hfA : ∀ stmt td, (R₁.append R₂).verifier.verify stmt td =
      (pure (f₂ (f₁ stmt td.fst) td.snd) : OptionT (OracleComp oSpec) Stmt₃) := by
    intro stmt td
    show (do
      let stmt₂ ← R₁.verifier.verify stmt td.fst
      let r ← R₂.verifier.verify stmt₂ td.snd
      pure r : OptionT (OracleComp oSpec) Stmt₃) = _
    rw [hf₁, pure_bind, hf₂]
    simp only [bind_pure]
  -- Composed-run characterization through the appended prover.
  have hcomp := Reduction.run_pure_verifier (R₁.append R₂)
    (fun stmt td => f₂ (f₁ stmt td.fst) td.snd) hfA stmtIn witIn
  simp only [hcomp]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  -- Extract stage facts from h₁ at init.
  have h₁' := h₁ stmtIn witIn hIn
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff] at h₁'
  simp only [Reduction.run_pure_verifier R₁ f₁ hf₁] at h₁'
  obtain ⟨-, h₁supp⟩ := h₁'
  -- Per-state stage-1 prover facts (constructive membership into h₁supp's support).
  have h₁supp' : ∀ s ∈ _root_.support init,
      ∀ q ∈ _root_.support (StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (R₁.prover.run stmtIn witIn) :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s),
      (f₁ stmtIn q.1.1, q.1.2.2) ∈ rel₂ ∧ q.1.2.1 = f₁ stmtIn q.1.1 := by
    intro s hs q hq
    exact h₁supp ((q.1.1, q.1.2), f₁ stmtIn q.1.1) (by
      rw [OptionT.mem_support_iff]
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
      refine ⟨s, hs, ?_⟩
      simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map, support_bind,
        Set.mem_image, Set.mem_iUnion, exists_prop]
      exact ⟨(some ((q.1.1, q.1.2), f₁ stmtIn q.1.1), q.2),
        ⟨q, hq, by simp [simulateQ_pure, StateT.run_pure]⟩, rfl⟩)
  constructor
  · -- No failure: the composed value is unconditionally `some`.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ h
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind] at h
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at h
    obtain ⟨p, ⟨r, _, hp⟩, hnone⟩ := h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp] at hnone
    exact Option.some_ne_none _ hnone
  · -- Support ⊆ event: decompose through hfact, compose event₁ and event₂.
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, hs, hx⟩ := hx
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind] at hx
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨p, ⟨r, hr, hp⟩, hsome⟩ := hx
    rw [hfact stmtIn witIn s] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hr
    obtain ⟨q₁, hq₁, q₂, hq₂, hr_eq⟩ := hr
    obtain ⟨hrel₂, hstmt₂⟩ := h₁supp' s hs q₁ hq₁
    -- Stage-2 facts from h₂ at the deterministic mid state.
    have h₂' := h₂ (pure q₁.2) q₁.1.2.1 q₁.1.2.2 (by rw [hstmt₂]; exact hrel₂)
    rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff] at h₂'
    simp only [Reduction.run_pure_verifier R₂ f₂ hf₂] at h₂'
    obtain ⟨-, h₂supp⟩ := h₂'
    have hev₂ := h₂supp ((q₂.1.1, q₂.1.2), f₂ q₁.1.2.1 q₂.1.1) (by
      rw [OptionT.mem_support_iff]
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
      refine ⟨q₁.2, by simp, ?_⟩
      simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map, support_bind,
        Set.mem_image, Set.mem_iUnion, exists_prop]
      exact ⟨(some ((q₂.1.1, q₂.1.2), f₂ q₁.1.2.1 q₂.1.1), q₂.2),
        ⟨q₂, hq₂, by simp [simulateQ_pure, StateT.run_pure]⟩, rfl⟩)
    obtain ⟨hrel₃, hstmt₃⟩ := hev₂
    -- Assemble the composed event.
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp] at hsome
    cases Option.some.inj hsome
    rw [hr_eq]
    refine ⟨?_, ?_⟩
    · show (f₂ (f₁ stmtIn (q₁.1.1 ++ₜ q₂.1.1).fst) (q₁.1.1 ++ₜ q₂.1.1).snd, q₂.1.2.2) ∈ rel₃
      rw [FullTranscript.append_fst, FullTranscript.append_snd, ← hstmt₂]
      exact hrel₃
    · show q₂.1.2.1 = f₂ (f₁ stmtIn (q₁.1.1 ++ₜ q₂.1.1).fst) (q₁.1.1 ++ₜ q₂.1.1).snd
      rw [FullTranscript.append_fst, FullTranscript.append_snd, ← hstmt₂]
      exact hstmt₃

end AppendCompleteness
