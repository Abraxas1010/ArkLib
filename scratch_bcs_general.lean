/- LANE D: general-arity BCS completeness — discharge #635's hfact via
   append_run_of_challenge_free. STATUS 2026-07-12: the D-brick (simulateQ/addLift
   routing coherence across the challenge-sum inclusion) is proven for the
   induction structure + continuations (ih fires); TWO bounded residual goals
   remain, both single-query evaluations (see FRONTIER sorries inline). Once the
   brick closes, hfact (#635's factorization hypothesis) discharges at general
   arity by rewriting with append_run_of_challenge_free_liftM + this brick ×2 +
   state-threading, yielding append_perfectCompleteness_of_challenge_free — the
   T1 keystone. Branch: feat/bcs-completeness-general (= #643 stack + #635). -/
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.AppendRun

open ProtocolSpec OracleSpec OracleComp

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- D-brick probe (left inclusion): routing a component computation through the
-- composed challenge sum and simulating there = simulating in its own sum.
example {β : Type} (x : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) β) :
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
      simp [QueryImpl.addLift, OracleQuery.liftM_right_add_right_add_query,
        OracleQuery.liftM_right_add_right_add_def]
      sorry -- FRONTIER (bounded): simulateQ_app (liftM (query (Sum.inl q))) = impl q.
            -- The OC-level liftM-of-query must be exposed as the query-level lift
            -- (Add.lean liftM_right_add_right_add_query applies at OracleQuery level;
            -- need the OC bridge: single-query lift = lift-query-then-embed normal
            -- form per SubSpec.lean's priority docs), then simulateQ_query + addLift
            -- at inl evaluates to impl q on both sides.
    | inr q =>
      simp only [liftComp_bind, liftComp_query, ih, simulateQ_bind, simulateQ_query]
      simp [QueryImpl.addLift, OracleQuery.liftM_right_add_right_add_query,
        OracleQuery.liftM_right_add_right_add_def]
      sorry -- FRONTIER (the content-bearing goal): simulateQ_app of the lifted
            -- challenge query = challengeQueryImpl₁ q. After the same OC-bridge,
            -- reduces to: cast (Challenge_inl j) <$> ($ᵗ Challenge_app(inl j))
            -- = $ᵗ Challenge₁ j — the sampling/instance alignment across the
            -- type equality (the crown's pinning hazard at the simulateQ level,
            -- now isolated to ONE uniform-sampling-transport lemma).
