/- LANE D — COMPLETE (2026-07-12). THE T1 KEYSTONE IS PROVEN:
   `append_perfectCompleteness_of_challenge_free` — completeness composes for
   the challenge-free (commitment-transform / BCS) class at fully general
   arity (m ≥ 0 × n ≥ 1), with pure verifiers, unconditionally in the
   factorization. All results at [propext, Classical.choice, Quot.sound]
   (#print axioms, transitively sorryAx-free).

   Chain: D0 uniformSample_cast + cast_arrow_apply (sampling transport) →
   simulateQ_addLift_liftComp_left/right (the routing bricks — the crown's
   erw-hazard as two induction lemmas; instance alignment via fappend₂_left/
   right) → hfact_of_challenge_free (#635's factorization hypothesis at
   general arity: rewrite by append_run_of_challenge_free, bricks collapse
   the lifts, rfl) → the keystone (#635's composition theorem applied).

   Branch: feat/bcs-completeness-general (= #643 stack ⊕ #635). Upstreaming:
   promote to a module in the PR that stacks on #635+#643 once those merge. -/
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.AppendRun

open ProtocolSpec OracleSpec OracleComp

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [h₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
  [h₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **D0 (sampling transport)**: uniform sampling commutes with a type-equality
cast when the two `SampleableType` instances are heq-aligned. -/
theorem uniformSample_cast {A B : Type} (h : B = A)
    {iB : SampleableType B} {iA : SampleableType A} (hi : HEq iB iA) :
    (_root_.cast h <$> ($ᵗ B) : ProbComp A) = $ᵗ A := by
  subst h
  cases eq_of_heq hi
  exact id_map _

/-- Pointwise dissolution of a cast between arrow-types over propositionally
equal domains and equal codomains. -/
theorem cast_arrow_apply {P Q : Prop} {T U : Type} (hP : P = Q) (h : T = U)
    (e : (P → T) = (Q → U)) (f : P → T) (q : Q) :
    HEq (_root_.cast e f q) (f (hP ▸ q)) := by
  subst hP; subst h; rfl

-- D-brick (left inclusion): routing a component computation through the
-- composed challenge sum and simulating there = simulating in its own sum.
theorem simulateQ_addLift_liftComp_left {β : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (x : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) β) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
      (liftComp x (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
    = simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) x := by
  induction x using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih =>
    cases t with
    | inl q =>
      simp only [liftComp_bind, liftComp_query, ih, simulateQ_bind, simulateQ_query]
      have hsrc : (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
          (liftComp (((OracleSpec.query (Sum.inl q) :
              OracleQuery (oSpec + [pSpec₁.Challenge]ₒ)
                ((oSpec + [pSpec₁.Challenge]ₒ).Range (Sum.inl q)))) :
              OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
          = impl q := by
        rw [show (liftComp (((OracleSpec.query (Sum.inl q) :
              OracleQuery (oSpec + [pSpec₁.Challenge]ₒ)
                ((oSpec + [pSpec₁.Challenge]ₒ).Range (Sum.inl q)))) :
              OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
          = (liftM ((liftM (OracleSpec.query (Sum.inl q)) :
              OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                ((oSpec + [pSpec₁.Challenge]ₒ).Range (Sum.inl q)))) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
        rw [OracleQuery.liftM_right_add_right_add_query]
        show simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query (Sum.inl q)))
          = impl q
        rw [simulateQ_spec_query]
        rfl
      rw [← liftComp_query, hsrc]
      simp [QueryImpl.addLift]
    | inr q =>
      simp only [liftComp_bind, liftComp_query, ih, simulateQ_bind, simulateQ_query]
      congr 1
      show simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (((liftM (OracleSpec.query (Sum.inr q)) :
            OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((oSpec + [pSpec₁.Challenge]ₒ).Range (Sum.inr q))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _))
        = _
      rw [OracleQuery.liftM_right_add_right_add_query]
      simp [QueryImpl.addLift]
      obtain ⟨j, u⟩ := q
      show (fun (r : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl j)) =>
          (_root_.cast (ProtocolSpec.Challenge_inl j) r)) <$>
          (liftM ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl j))) :
            StateT σ ProbComp ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl j)))
        = liftM ($ᵗ (pSpec₁.Challenge j))
      have hnat : ∀ {γ δ : Type} (f : γ → δ) (x : ProbComp γ),
          (f <$> (liftM x : StateT σ ProbComp γ) : StateT σ ProbComp δ)
            = liftM (f <$> x) := by
        intro γ δ f x
        funext st
        show (f <$> (liftM x : StateT σ ProbComp γ)).run st
          = ((liftM (f <$> x) : StateT σ ProbComp δ)).run st
        simp [StateT.run_map, Functor.map_map]
      rw [hnat]
      refine congrArg liftM (uniformSample_cast (ProtocolSpec.Challenge_inl j) ?_)
      have hdir : ((pSpec₁.dir ++ᵛ pSpec₂.dir) (Fin.castAdd n j.1) = Direction.V_to_P)
          = (pSpec₁.dir j.1 = Direction.V_to_P) := by
        rw [Fin.vappend_eq_append, Fin.append_left]
      have hty : SampleableType ((pSpec₁.«Type» ++ᵛ pSpec₂.«Type») (Fin.castAdd n j.1))
          = SampleableType (pSpec₁.«Type» j.1) := by
        rw [Fin.vappend_eq_append, Fin.append_left]
      show HEq
        ((Fin.fappend₂ (F := fun dir type => dir = Direction.V_to_P → SampleableType type)
          (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) (Fin.castAdd n j.1))
          (hdir.symm ▸ j.2))
        (h₁ j)
      rw [Fin.fappend₂_left]
      exact cast_arrow_apply hdir.symm hty.symm _ (fun h => h₁ ⟨j.1, h⟩) (hdir.symm ▸ j.2)
-- D-brick (right inclusion): mirror of the left brick for the second component.
theorem simulateQ_addLift_liftComp_right {β : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (x : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) β) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
      (liftComp x (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
    = simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp)) x := by
  induction x using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih =>
    cases t with
    | inl q =>
      simp only [liftComp_bind, liftComp_query, ih, simulateQ_bind, simulateQ_query]
      have hsrc : (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
          (liftComp (((OracleSpec.query (Sum.inl q) :
              OracleQuery (oSpec + [pSpec₂.Challenge]ₒ)
                ((oSpec + [pSpec₂.Challenge]ₒ).Range (Sum.inl q)))) :
              OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
          = impl q := by
        rw [show (liftComp (((OracleSpec.query (Sum.inl q) :
              OracleQuery (oSpec + [pSpec₂.Challenge]ₒ)
                ((oSpec + [pSpec₂.Challenge]ₒ).Range (Sum.inl q)))) :
              OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
          = (liftM ((liftM (OracleSpec.query (Sum.inl q)) :
              OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                ((oSpec + [pSpec₂.Challenge]ₒ).Range (Sum.inl q)))) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
        rw [OracleQuery.liftM_right_add_right_add_query]
        show simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query (Sum.inl q)))
          = impl q
        rw [simulateQ_spec_query]
        rfl
      rw [← liftComp_query, hsrc]
      simp [QueryImpl.addLift]
    | inr q =>
      simp only [liftComp_bind, liftComp_query, ih, simulateQ_bind, simulateQ_query]
      congr 1
      show simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (((liftM (OracleSpec.query (Sum.inr q)) :
            OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((oSpec + [pSpec₂.Challenge]ₒ).Range (Sum.inr q))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _))
        = _
      rw [OracleQuery.liftM_right_add_right_add_query]
      simp [QueryImpl.addLift]
      obtain ⟨j, u⟩ := q
      show (fun (r : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr j)) =>
          (_root_.cast (ProtocolSpec.Challenge_inr j) r)) <$>
          (liftM ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr j))) :
            StateT σ ProbComp ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr j)))
        = liftM ($ᵗ (pSpec₂.Challenge j))
      have hnat : ∀ {γ δ : Type} (f : γ → δ) (x : ProbComp γ),
          (f <$> (liftM x : StateT σ ProbComp γ) : StateT σ ProbComp δ)
            = liftM (f <$> x) := by
        intro γ δ f x
        funext st
        show (f <$> (liftM x : StateT σ ProbComp γ)).run st
          = ((liftM (f <$> x) : StateT σ ProbComp δ)).run st
        simp [StateT.run_map, Functor.map_map]
      rw [hnat]
      refine congrArg liftM (uniformSample_cast (ProtocolSpec.Challenge_inr j) ?_)
      have hdir : ((pSpec₁.dir ++ᵛ pSpec₂.dir) (Fin.natAdd m j.1) = Direction.V_to_P)
          = (pSpec₂.dir j.1 = Direction.V_to_P) := by
        rw [Fin.vappend_eq_append, Fin.append_right]
      have hty : SampleableType ((pSpec₁.«Type» ++ᵛ pSpec₂.«Type») (Fin.natAdd m j.1))
          = SampleableType (pSpec₂.«Type» j.1) := by
        rw [Fin.vappend_eq_append, Fin.append_right]
      show HEq
        ((Fin.fappend₂ (F := fun dir type => dir = Direction.V_to_P → SampleableType type)
          (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) (Fin.natAdd m j.1))
          (hdir.symm ▸ j.2))
        (h₂ j)
      rw [Fin.fappend₂_right]
      exact cast_arrow_apply hdir.symm hty.symm _ (fun h => h₂ ⟨j.1, h⟩) (hdir.symm ▸ j.2)
/-! ## hfact at general arity: #635's prover-factorization hypothesis,
    discharged for challenge-free protocols via `append_run_of_challenge_free`
    + the two routing bricks. -/

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}

theorem hfact_of_challenge_free
    {n' : ℕ} {pSpec₂' : ProtocolSpec (n' + 1)}
    [h₂' : ∀ i, SampleableType (pSpec₂'.Challenge i)]
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂' : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hCF₁ : ∀ i, pSpec₁.dir i = .P_to_V) (hCF₂ : ∀ i, pSpec₂'.dir i = .P_to_V)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp))
      (liftM ((P₁.append P₂').run stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _)) s
    = (do
      let (r₁, s₁) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (P₁.run stmt wit) :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s
      let (r₂, s₂) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (P₂'.run r₁.2.1 r₁.2.2) :
          OracleComp (oSpec + [pSpec₂'.Challenge]ₒ) _)) s₁
      pure ((r₁.1 ++ₜ r₂.1, r₂.2), s₂)) := by
  rw [show (liftM ((P₁.append P₂').run stmt wit) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _)
    = (P₁.append P₂').run stmt wit from rfl]
  rw [AppendGeneral.append_run_of_challenge_free P₁ P₂' hCF₁ hCF₂ stmt wit]
  rw [show (liftM (P₁.run stmt wit) : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
    = P₁.run stmt wit from rfl]
  simp only [simulateQ_bind, simulateQ_addLift_liftComp_left,
    simulateQ_addLift_liftComp_right, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rfl

/-! ## THE T1 KEYSTONE: completeness composes for the challenge-free class,
    at fully general arity — #635's composition theorem with the prover
    factorization discharged by `append_run_of_challenge_free`. -/

theorem append_perfectCompleteness_of_challenge_free
    {n' : ℕ} {pSpec₂' : ProtocolSpec (n' + 1)}
    [h₂' : ∀ i, SampleableType (pSpec₂'.Challenge i)]
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hCF₁ : ∀ i, pSpec₁.dir i = .P_to_V) (hCF₂ : ∀ i, pSpec₂'.dir i = .P_to_V)
    (f₁ : Stmt₁ → FullTranscript pSpec₁ → Stmt₂)
    (f₂ : Stmt₂ → FullTranscript pSpec₂' → Stmt₃)
    (hf₁ : ∀ stmt td, R₁.verifier.verify stmt td =
      (pure (f₁ stmt td) : OptionT (OracleComp oSpec) Stmt₂))
    (hf₂ : ∀ stmt td, R₂.verifier.verify stmt td =
      (pure (f₂ stmt td) : OptionT (OracleComp oSpec) Stmt₃))
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ init' : ProbComp σ, R₂.perfectCompleteness init' impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  Reduction.append_perfectCompleteness_of_proverFactorization R₁ R₂ f₁ f₂ hf₁ hf₂
    (fun stmt wit s =>
      hfact_of_challenge_free R₁.prover R₂.prover hCF₁ hCF₂ impl stmt wit s)
    h₁ h₂

/-! ## Message-opening generality: the keystone with challenges allowed
    everywhere except the right protocol's opening round. -/

theorem hfact_of_message_opening
    {n' : ℕ} {pSpec₂' : ProtocolSpec (n' + 1)}
    [h₂' : ∀ i, SampleableType (pSpec₂'.Challenge i)]
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂' : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hop : pSpec₂'.dir ⟨0, by omega⟩ = .P_to_V)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp))
      (liftM ((P₁.append P₂').run stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _)) s
    = (do
      let (r₁, s₁) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (P₁.run stmt wit) :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s
      let (r₂, s₂) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (P₂'.run r₁.2.1 r₁.2.2) :
          OracleComp (oSpec + [pSpec₂'.Challenge]ₒ) _)) s₁
      pure ((r₁.1 ++ₜ r₂.1, r₂.2), s₂)) := by
  rw [show (liftM ((P₁.append P₂').run stmt wit) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _)
    = (P₁.append P₂').run stmt wit from rfl]
  rw [AppendGeneral.append_run_of_message_opening P₁ P₂' hop stmt wit]
  rw [show (liftM (P₁.run stmt wit) : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
    = P₁.run stmt wit from rfl]
  simp only [simulateQ_bind, simulateQ_addLift_liftComp_left,
    simulateQ_addLift_liftComp_right, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rfl

/-! ## THE T1 KEYSTONE: completeness composes for the challenge-free class,
    at fully general arity — #635's composition theorem with the prover
    factorization discharged by `append_run_of_challenge_free`. -/

theorem append_perfectCompleteness_of_message_opening
    {n' : ℕ} {pSpec₂' : ProtocolSpec (n' + 1)}
    [h₂' : ∀ i, SampleableType (pSpec₂'.Challenge i)]
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hop : pSpec₂'.dir ⟨0, by omega⟩ = .P_to_V)
    (f₁ : Stmt₁ → FullTranscript pSpec₁ → Stmt₂)
    (f₂ : Stmt₂ → FullTranscript pSpec₂' → Stmt₃)
    (hf₁ : ∀ stmt td, R₁.verifier.verify stmt td =
      (pure (f₁ stmt td) : OptionT (OracleComp oSpec) Stmt₂))
    (hf₂ : ∀ stmt td, R₂.verifier.verify stmt td =
      (pure (f₂ stmt td) : OptionT (OracleComp oSpec) Stmt₃))
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ init' : ProbComp σ, R₂.perfectCompleteness init' impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  Reduction.append_perfectCompleteness_of_proverFactorization R₁ R₂ f₁ f₂ hf₁ hf₂
    (fun stmt wit s =>
      hfact_of_message_opening R₁.prover R₂.prover hop impl stmt wit s)
    h₁ h₂
