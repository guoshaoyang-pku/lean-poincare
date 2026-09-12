import Poincare.D12.KappaVariational.All

/-- Negative control for the fail-closed audit: an intentional project axiom. -/
axiom badProjectAxiom : False

theorem badTheorem : False := badProjectAxiom

#print axioms badProjectAxiom
#print axioms badTheorem
