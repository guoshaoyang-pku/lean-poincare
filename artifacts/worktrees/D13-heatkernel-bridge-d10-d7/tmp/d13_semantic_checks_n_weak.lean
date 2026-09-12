-- D13 thirteenth invocation: semantic transcript for the weak (test-paired) heat equation on the
-- corrected admissible-test-function domain.
import Poincare.D13.HeatKernelBridge.WeakHeatEquation
import Poincare.D13.HeatKernelBridge.WeakFinite
import Poincare.D7.HeatKernel.WeakStatus

open MeasureTheory Filter
open scoped Topology

-- the versioned weak predicate and its structure
#check @Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.v1
#check @Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE
#print Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE

-- the analytic certificates (the manifold-side obligation made explicit)
#check @Poincare.D13.HeatKernelBridge.WeakHeatCertificates
#print Poincare.D13.HeatKernelBridge.WeakHeatCertificates

-- the transfer: pointwise PDE + certificates => weak equation
#check @Poincare.D13.HeatKernelBridge.weakHeatKernelPDE_of_hasDerivAt
#check @Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.toWeak
#check @Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.hasDerivAt
#check @Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.mono_class

-- the flat Gaussian bounds used for the certificates
#check @Poincare.D13.HeatKernelBridge.rpow_neg_half_le_of_le
#check @Poincare.D13.HeatKernelBridge.mul_exp_neg_le_inv_e
#check @Poincare.D13.HeatKernelBridge.gaussianKernel_le_prefactor
#check @Poincare.D13.HeatKernelBridge.gaussianKernel_abs_le_prefactor
#check @Poincare.D13.HeatKernelBridge.flatKernel_abs_le_prefactor
#check @Poincare.D13.HeatKernelBridge.flatLaplacianBound
#check @Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian_apply
#check @Poincare.D13.HeatKernelBridge.flatKernel_continuous_snapshot
#check @Poincare.D13.HeatKernelBridge.flatKernel_laplacian_continuous_snapshot
#check @Poincare.D13.HeatKernelBridge.gaussianKernel_mul_sq_div_le
#check @Poincare.D13.HeatKernelBridge.flatKernel_laplacian_abs_le

-- the flat certificates and the flat weak equation in both classes
#check @Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_of_subclass
#check @Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_integrable
#check @Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_cc
#check @Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_integrable
#check @Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_cc
#check @Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_of_subclass
#check @Poincare.D13.HeatKernelBridge.flat_weak_snapshot_refuted

-- the pinned finite model (second, non-flat model of the weak interface)
#check @Poincare.D13.HeatKernelBridge.finiteLaplacianBound
#check @Poincare.D13.HeatKernelBridge.finiteLaplacianBound_nonneg
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_abs_le_one
#check @Poincare.D13.HeatKernelBridge.finiteHeatKernel_laplacian_abs_le
#check @Poincare.D13.HeatKernelBridge.finiteWeakHeatCertificates
#check @Poincare.D13.HeatKernelBridge.finite_weakHeatKernel
#check @Poincare.D13.HeatKernelBridge.finite_weak_and_pde_inhabited

-- D7-level consumption
#check @Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime
#check @Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_volume
#check @Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_laplacian
#check @Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_timeDerivative
#check @Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_dist
#check @Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_dim
#check @Poincare.D7.HeatKernel.heatKernelData_weakHeatEquation
#check @Poincare.D7.HeatKernel.heatKernelDataV1_weakHeatEquation
#check @Poincare.D7.HeatKernel.flat_weakHeatEquation_integrable
#check @Poincare.D7.HeatKernel.flat_weakHeatEquation_cc
#check @Poincare.D7.HeatKernel.flat_weak_and_snapshot_refuted
#check @Poincare.D7.HeatKernel.weak_status_summary
#check @Poincare.D7.HeatKernel.finite_weakHeatEquation
