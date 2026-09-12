/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D9-tensor-algebra-manifolds)
-/
import Poincare.D9.TensorAlgebra.Interface
import Poincare.D9.TensorAlgebra.Props
import Poincare.D9.TensorAlgebra.Toy

/-!
# Poincare.D9.TensorAlgebra.AxiomAudit

`#print axioms` audit for every declaration authored by task
`D9-tensor-algebra-manifolds`.

The output below is exactly what the Lean kernel reports for each declaration (possibly
modulo the standard `propext` / `Classical.choice` / `Quot.sound` trio already accepted by
the D6 weekly release).  Any proof hole, postulated constant or native-evaluation shortcut
would show up here immediately.
-/

#print axioms Poincare.D9.TensorAlgebra.TensorBundleData
#print axioms Poincare.D9.TensorAlgebra.contract_smooth
#print axioms Poincare.D9.TensorAlgebra.metricTrace_smooth
#print axioms Poincare.D9.TensorAlgebra.flat_smooth
#print axioms Poincare.D9.TensorAlgebra.sharp_smooth
#print axioms Poincare.D9.TensorAlgebra.tensorProduct_smooth
#print axioms Poincare.D9.TensorAlgebra.metric_smooth
#print axioms Poincare.D9.TensorAlgebra.pullback_smooth
#print axioms Poincare.D9.TensorAlgebra.contract_pullback_comm
#print axioms Poincare.D9.TensorAlgebra.IsMetricPreserving
#print axioms Poincare.D9.TensorAlgebra.metricTrace_pullback_comm
#print axioms Poincare.D9.TensorAlgebra.flat_pullback_comm
#print axioms Poincare.D9.TensorAlgebra.sharp_pullback_comm
#print axioms Poincare.D9.TensorAlgebra.TraceDivergenceInterface
#print axioms Poincare.D9.TensorAlgebra.trace_divergence_identity

#print axioms Poincare.D9.TensorAlgebra.Toy.flat
#print axioms Poincare.D9.TensorAlgebra.Toy.sharp
#print axioms Poincare.D9.TensorAlgebra.Toy.sharp_flat
#print axioms Poincare.D9.TensorAlgebra.Toy.flat_sharp
#print axioms Poincare.D9.TensorAlgebra.Toy.metric
#print axioms Poincare.D9.TensorAlgebra.Toy.metric_apply
#print axioms Poincare.D9.TensorAlgebra.Toy.metricTrace_metric_eq_finrank
#print axioms Poincare.D9.TensorAlgebra.Toy.trace_sharp_comp_flat
#print axioms Poincare.D9.TensorAlgebra.Toy.inverseMetric
#print axioms Poincare.D9.TensorAlgebra.Toy.inverseMetric_apply
#print axioms Poincare.D9.TensorAlgebra.Toy.metricTrace_inverseMetric_eq_finrank
#print axioms Poincare.D9.TensorAlgebra.Toy.dualPairing
#print axioms Poincare.D9.TensorAlgebra.Toy.dualPairing_eq_inner
#print axioms Poincare.D9.TensorAlgebra.Toy.tensorProductOneForm
#print axioms Poincare.D9.TensorAlgebra.Toy.contract_tensorProduct
#print axioms Poincare.D9.TensorAlgebra.Toy.contract_tensorProduct_eq_inner
