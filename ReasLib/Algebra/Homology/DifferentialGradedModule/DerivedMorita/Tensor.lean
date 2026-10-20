module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.FullyFaithful
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Kernel
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Concentrated
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Equivalence
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence

/-!
# DG Morita Equivalences Realized by Tensor Functors

This leaf is the differential-graded core of tensor realization for derived Morita theory.  It
does not depend on ordinary algebras or on the degree-zero comparison.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainDGAlgebra.DerivedMorita

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

namespace Tensor

/-- Lemma 22.37.2 (09S7): the concrete derived tensor functor of a DG bimodule is an
equivalence when the represented right module is compact, weakly generates, and has the
prescribed shifted self-extensions. -/
@[stacks 09S7]
theorem isEquivalence_of_compactGenerator
    (N : DifferentialGradedBimodule A B)
    (h_compact : IsCompactObject N.rightDerivedObject)
    (h_generator : IsWeakGenerator N.rightDerivedObject)
    (h_selfExt : N.HasSelfExtComparison) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence := sorry

/-- Derived tensoring by a Morita kernel is an equivalence. -/
@[stacks 09S7 "derived tensor equivalence of a Morita kernel"]
theorem isEquivalence
    (N : DifferentialGradedBimodule A B) (hN : N.IsMoritaKernel) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence := sorry

/-- Derived tensoring by a Morita kernel, bundled as an `R`-linear triangulated equivalence.
This is the data-level form of `isEquivalence`, suitable for transport and composition. -/
@[stacks 09S7 "linear triangulated equivalence of a Morita kernel"]
noncomputable def equivalence
    (N : DifferentialGradedBimodule A B) (hN : N.IsMoritaKernel) :
    RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category A)
      (DifferentialGradedModule.Derived.Category B) :=
  RLinear.TriangulatedEquivalence.ofAdjunction R
    (DifferentialGradedBimodule.TensorHom.derivedAdjunction N)
    (isEquivalence N hN)

/-- The forward functor of the Morita equivalence is derived tensoring by its kernel. -/
@[simp, stacks 09S7 "forward functor of a Morita-kernel equivalence"]
theorem equivalence_functor
    (N : DifferentialGradedBimodule A B) (hN : N.IsMoritaKernel) :
      (equivalence N hN).functor =
      DifferentialGradedBimodule.Tensor.derivedFunctor N := sorry

/-- The inverse of the Morita equivalence is the derived internal-Hom functor of its kernel.
Unlike an arbitrary quasi-inverse, this presentation is stable under composition and exposes the
adjunction used by downstream Hom computations. -/
@[stacks 09S7 "derived internal-Hom inverse of a Morita equivalence"]
theorem equivalence_inverse
    (N : DifferentialGradedBimodule A B) (hN : N.IsMoritaKernel) :
    (equivalence N hN).inverse =
      DifferentialGradedBimodule.InternalHom.derivedFunctor N := sorry

/-- The concrete derived tensor functor is an equivalence when its represented bimodule object
classically generates the compact objects and has the prescribed shifted self-extensions. -/
@[stacks 09SS "classical-generator criterion for concrete derived tensor"]
theorem isEquivalence_of_classicalGenerator
    (N : DifferentialGradedBimodule A B)
    (h_compact : IsCompactObject N.rightDerivedObject)
    (h_classical : IsClassicalGeneratorOfCompacts N.rightDerivedObject)
    (h_selfExt : N.HasSelfExtComparison) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence := sorry

/-- The concrete derived tensor functor is an equivalence under the weak compact-generator
criterion when derived internal Hom of the target regular object is compact. -/
@[stacks 09SS "weak compact-generator criterion for concrete derived tensor"]
theorem isEquivalence_of_weakCompactGenerator
    (N : DifferentialGradedBimodule A B)
    (h_compact : IsCompactObject N.rightDerivedObject)
    (h_rHom_regular : IsCompactObject
      ((DifferentialGradedBimodule.InternalHom.derivedFunctor N).obj
        (DifferentialGradedModule.Derived.regularObject B)))
    (h_generator : IsWeakGeneratorOfCompacts N.rightDerivedObject)
    (h_selfExt : N.HasSelfExtComparison) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence := sorry

end Tensor

/-- Derived Morita equivalence between DG algebras is equivalent to realization by derived
tensoring with a DG bimodule when the source is concentrated in degree zero and the target is
K-flat. -/
@[stacks 09SC "DG Morita equivalence realized by derived tensor"]
theorem nonempty_equivalence_iff_exists_tensor
    (A B : CochainDGAlgebra.{u, v} R)
    (hA : A.IsConcentratedInDegreeZero) (hB : B.IsKFlat) :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category A)
      (DifferentialGradedModule.Derived.Category B)) ↔
      ∃ N : DifferentialGradedBimodule A B,
        (DifferentialGradedBimodule.Tensor.derivedFunctor N).IsEquivalence := sorry

end CochainDGAlgebra.DerivedMorita
