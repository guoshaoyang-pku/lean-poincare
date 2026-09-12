import Poincare.D12.SemanticLedger.LedgerProbe

/-! Round-7 audit self-control: deliberately defective declarations.
This file exists only in a throwaway copy and is never evidence about a card. -/

namespace Poincare
namespace D12
namespace SemanticLedger

axiom a3CtlAxiom : False

theorem a3CtlAxiomTheorem : False := a3CtlAxiom

theorem a3CtlSorryTheorem : False := by
  sorry

theorem a3CtlTauto (P : Prop) (h : P) : P := h

end SemanticLedger
end D12
end Poincare
