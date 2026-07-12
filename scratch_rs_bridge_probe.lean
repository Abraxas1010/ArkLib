/- T2.S1 scratch probe (NOT for PR): BHK witness that the CompPoly→ArkLib RS bridge
   THEOREM STATEMENT elaborates. CAVEAT (census receipt): ArkLib's pinned CompPoly rev
   18c1613 predates CompPoly/Univariate/ReedSolomon.lean, so `encode`/`Domain` are
   MIRRORED inline below from CompPoly HEAD e95ba1b source (type-faithful, 1:1); the
   real bridge file imports them after the pin bump that PR #574 already carries. -/
import ArkLib.Data.CodingTheory.ReedSolomon

section probe

variable {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]

/-- Mirror of CompPoly.ReedSolomon.Domain (HEAD e95ba1b): nodup evaluation-point array. -/
def CDomain (F : Type*) := {a : Array F // a.toList.Nodup}

def CDomain.n (D : CDomain F) : ℕ := D.val.size

/-- Mirror of CompPoly.ReedSolomon.Domain.node_injective. -/
lemma CDomain.node_injective (D : CDomain F) :
    Function.Injective (fun i : Fin D.n => D.val[i]) :=
  fun _ _ hxy => Fin.ext ((List.getElem_inj D.property).mp hxy)

/-- The embedding induced by a CompPoly evaluation domain — the bridge's first brick. -/
def domainEmb (D : CDomain F) : Fin D.n ↪ F :=
  ⟨fun i => D.val[i], CDomain.node_injective D⟩

/-- STATEMENT PROBE (core type alignment): an executable codeword (any
`Vector F D.n`, e.g. CompPoly's `encode D msg`), read back as a function
`Fin D.n → F`, is a member of ArkLib's noncomputable Reed-Solomon code over the
induced embedding. Elaboration of this Prop is the witness that the two sides'
types meet; the PROOF (via `messagePoly.toPoly`, `messagePoly_degree_lt`,
`CPolynomial.eval_toPoly`) is T2.S2. -/
def bridgeStatement (D : CDomain F) (k : ℕ) (v : Vector F D.n) : Prop :=
  (fun i => v.get i) ∈ ReedSolomon.code (domainEmb D) k

/-- STATEMENT PROBE (T2.S3 shape): plain-order NTT output agrees pointwise with the
executable encoding; `NTTFast` needs `bitRevPermute` composition (census receipt:
`forwardImpl_eq_bitRevPermute_evalOnDomain`, NTTFast/Correctness.lean:29). -/
def nttBridgeStatement (D : CDomain F) (nttOut encWord : Vector F D.n) : Prop :=
  ∀ i : Fin D.n, nttOut.get i = encWord.get i

end probe
