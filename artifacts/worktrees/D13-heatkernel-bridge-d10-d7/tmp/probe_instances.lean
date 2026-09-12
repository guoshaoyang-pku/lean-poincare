import Mathlib
open MeasureTheory

-- which instances exist for Bool / Fin 2 / PUnit ⊕ PUnit
example : TopologicalSpace Bool := inferInstance
example : MeasurableSpace Bool := inferInstance
example : BorelSpace Bool := inferInstance
example : MeasurableSingletonClass Bool := inferInstance
example : CompactSpace Bool := inferInstance
example : Finite Bool := inferInstance
