/- T1.S1 scratch probe (NOT for PR): BHK witness that the BCS-as-QueryImpl shape
   type-checks against ArkLib head. Mirrors OracleVerifier.toVerifier
   (OracleReduction/Basic.lean:327) with the message side opening-backed. -/
import ArkLib.OracleReduction.Basic

open OracleSpec OracleComp ProtocolSpec OracleInterface

section probe

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  {ιₛ : Type} {OStmtIn : ιₛ → Type} [Oₛ : ∀ i, OracleInterface (OStmtIn i)]
  [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
  {StmtIn StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

/-- Opening-backed message oracle: answer each query to the prover's `i`-th oracle message
by running an opening procedure (in the ambient `OracleComp oSpec`) instead of reading
the message data. -/
def openingOracle
    (runOpening : ∀ (i : pSpec.MessageIdx) (q : (Oₘ i).Query),
      OracleComp oSpec ((Oₘ i).Response q)) :
    QueryImpl [pSpec.Message]ₒ (OracleComp oSpec) :=
  fun q => runOpening q.1 q.2

/-- The compiled simulation oracle: `simOracle2` with the message component opening-backed.
The `[OStmtIn]ₒ` side still answers from data (lifted pointwise into `OracleComp`). -/
def simOracleBCS (oStmt : ∀ i, OStmtIn i)
    (runOpening : ∀ (i : pSpec.MessageIdx) (q : (Oₘ i).Query),
      OracleComp oSpec ((Oₘ i).Response q)) :
    QueryImpl (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)) (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (QueryImpl.add
      (fun q => pure ((Oₛ q.1).answer (oStmt q.1) q.2))
      (openingOracle runOpening))

/-- The compiled verifier skeleton: `toVerifier` with `simOracle2` replaced by
`simOracleBCS`. Statement carries the input oracle data (still available to the verifier
in the reduction's compiled statement) and the opening runner is abstract at this stage. -/
def toVerifierViaOpenings
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (runOpening : ∀ (i : pSpec.MessageIdx) (q : (Oₘ i).Query),
      OracleComp oSpec ((Oₘ i).Response q)) :
    StmtIn → (∀ i, OStmtIn i) → pSpec.Challenges → OptionT (OracleComp oSpec) StmtOut :=
  fun stmt oStmt challenges =>
    simulateQ (simOracleBCS oStmt runOpening) (verifier.verify stmt challenges)

end probe
