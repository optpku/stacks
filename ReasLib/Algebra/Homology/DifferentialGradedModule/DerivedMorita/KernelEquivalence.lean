module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Tensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# DG Morita kernels and equivalences

This leaf records the information-preserving form of the DG Morita realization theorem.  The
existential witness is a bimodule equipped with its compact-generator and self-extension
certificate, so downstream tensor constructions can use the kernel directly.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v

namespace CochainDGAlgebra.DerivedMorita

variable {R : Type u} [CommRing R]

/-- Corollary of Proposition 22.37.6 (09SA) and Lemma 22.37.2 (09S7): under concentration of the
source and K-flatness of the target, an `R`-linear triangulated equivalence exists exactly when a
DG bimodule Morita kernel exists.  The kernel certificate is retained in the existential witness
and can be fed directly to `Tensor.equivalence`. -/
@[stacks 09SA "DG Morita equivalence detected by a Morita kernel",
  stacks 09S7 "tensor equivalence from a Morita kernel"]
theorem nonempty_equivalence_iff_exists_kernel
    (A B : CochainDGAlgebra.{u, v} R)
    (hA : A.IsConcentratedInDegreeZero) (hB : B.IsKFlat) :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category.{u, v} A)
      (DifferentialGradedModule.Derived.Category.{u, v} B)) ↔
      ∃ N : DifferentialGradedBimodule.{u, v, v, v} A B, N.IsMoritaKernel := sorry

end CochainDGAlgebra.DerivedMorita
