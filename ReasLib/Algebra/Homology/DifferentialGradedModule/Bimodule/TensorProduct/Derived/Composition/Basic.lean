module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Algebra.Composition
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue

/-!
# Composition of Derived Tensor Functors of DG Bimodules

This leaf owns the shape-independent composition API for derived tensor functors of differential
graded bimodules. It separates the canonical comparison for the explicit relative tensor
bimodule from the hypotheses under which that comparison is invertible.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.Tensor.Derived

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, v} R}

/-! The explicit relative-tensor composition owner currently uses one common carrier universe
`v` (the `Tensor.mapKAssociator` API has this boundary).  Accordingly this leaf writes the
four DGBimodule levels explicitly; the five universe levels of the derived tensor API are
instantiated as `.{u, v, v, v, v}` at this composition boundary. -/

/-- Equation 22.34.0.1 (0BZ2): the canonical comparison from derived tensoring by `N'`
at the right `B`-module underlying `N` to the corresponding ordinary relative tensor. -/
@[stacks 0BZ2 "derived-to-ordinary relative tensor comparison"]
noncomputable def ordinaryComparison
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    (derivedFunctor.{u, v, v, v, v} N').obj
        ((DifferentialGradedModule.Derived.Q.{u, v, v} B).obj ⟨N.toRightModule⟩) ⟶
      (DifferentialGradedModule.Derived.Q.{u, v, v} C).obj ⟨obj N.toRightModule N'⟩ :=
  (derivedCounit.{u, v, v, v, v} N').app ⟨N.toRightModule⟩

/-- The counit for successive derived tensoring, transported along the explicit associator of
relative tensor products to the source functor of `N ⊗_B N'`. -/
@[stacks 0BZ3 "transported counit for successive derived tensoring"]
noncomputable def compositeCounit
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    DifferentialGradedModule.Derived.Q.{u, v, v} A ⋙
        (derivedFunctor.{u, v, v, v, v} N ⋙
          derivedFunctor.{u, v, v, v, v} N') ⟶
      derivedSourceFunctor.{u, v, v, v, v}
        (bimodule.{u, v} N N') :=
  CategoryTheory.Functor.LeftDerived.Composition.iteratedCounit
      (derivedCounit.{u, v, v, v, v} N)
      (derivedCounit.{u, v, v, v, v} N') ≫
    (Functor.associator (dgFunctor N).mapK (dgFunctor N').mapK
      (DifferentialGradedModule.Derived.Q.{u, v, v} C)).inv ≫
    Functor.whiskerRight (mapKAssociator.{u, v} N N').hom
      (DifferentialGradedModule.Derived.Q.{u, v, v} C)

/-- The canonical comparison from successive derived tensoring to derived tensoring by the
explicit composite bimodule `N ⊗_B N'`. -/
@[stacks 0BZ8 "derived tensor composition comparison"]
noncomputable def comparison
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    derivedFunctor.{u, v, v, v, v} N ⋙
        derivedFunctor.{u, v, v, v, v} N' ⟶
      derivedFunctor.{u, v, v, v, v} (bimodule.{u, v} N N') :=
  (derivedFunctor.{u, v, v, v, v} (bimodule.{u, v} N N')).leftDerivedLift
    (derivedCounit.{u, v, v, v, v} (bimodule.{u, v} N N'))
    (DifferentialGradedModule.quasiIso.{u, v, v} A)
    (derivedFunctor.{u, v, v, v, v} N ⋙
      derivedFunctor.{u, v, v, v, v} N') (compositeCounit N N')

/-- The derived composition comparison factors the transported iterated counit through the
direct derived-tensor counit. -/
@[reassoc, stacks 0BZ3 "derived tensor composition comparison factorization"]
theorem comparison_fac
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) :
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q.{u, v, v} A)
        (comparison N N') ≫
      derivedCounit.{u, v, v, v, v} (bimodule.{u, v} N N') = compositeCounit N N' := sorry

/-- Invertibility of the pointwise derived-to-ordinary comparison at `N` promotes to
invertibility of the derived composition comparison. -/
@[stacks 0BZ3 "invertibility of the derived tensor composition comparison",
  stacks 0FTL "composition comparison for derived tensor functors"]
theorem comparison_isIso
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_ordinary : IsIso (ordinaryComparison N N')) :
    IsIso (comparison N N') := sorry

/-- Package an explicit proof that the derived composition comparison is invertible as the
corresponding natural isomorphism. Keeping the proof explicit avoids selecting inverse data
from an unrelated global instance. -/
@[stacks 0BZ3 "derived tensor composition isomorphism"]
noncomputable def comparisonIso
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_comparison : IsIso (comparison N N')) :
    derivedFunctor.{u, v, v, v, v} N ⋙
      derivedFunctor.{u, v, v, v, v} N' ≅
        derivedFunctor.{u, v, v, v, v} (bimodule.{u, v} N N') :=
  @asIso _ _ _ _ (comparison N N') h_comparison

/-- The forward map of `comparisonIso` is the canonical derived tensor comparison. -/
@[simp, stacks 0BZ3 "derived tensor comparison isomorphism forward map"]
theorem comparisonIso_hom
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_comparison : IsIso (comparison N N')) :
    (comparisonIso N N' h_comparison).hom = comparison N N' := sorry

/-- The inverse map of `comparisonIso` is the canonical inverse of the derived tensor comparison. -/
@[simp, stacks 0BZ3 "derived tensor comparison isomorphism inverse map"]
theorem comparisonIso_inv
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_comparison : IsIso (comparison N N')) :
    (comparisonIso N N' h_comparison).inv =
      @inv _ _ _ _ (comparison N N') h_comparison := sorry

/-- `comparisonIso` is independent of the proof chosen for invertibility. -/
@[stacks 0BZ3 "derived tensor comparison isomorphism proof independence"]
theorem comparisonIso_eq
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h₁ h₂ : IsIso (comparison N N')) :
    comparisonIso N N' h₁ = comparisonIso N N' h₂ := sorry

/-- A differential graded `(A, C)`-bimodule represents the composite of tensoring by `N` and
`N'` when its derived tensor functor is isomorphic to the composite derived functor. -/
@[stacks 0BZ8 "bimodule representation of derived tensor composition"]
abbrev RepresentsComposite
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (N'' : DifferentialGradedBimodule.{u, v, v, v} A C) : Prop :=
  Nonempty (derivedFunctor.{u, v, v, v, v} N ⋙
    derivedFunctor.{u, v, v, v, v} N' ≅
      derivedFunctor.{u, v, v, v, v} N'')

/-- The explicit relative tensor bimodule represents the composite whenever its canonical
comparison is invertible.  This is the direct, data-preserving form of the existential
composition criterion. -/
@[stacks 0BZ8 "explicit relative tensor represents derived composition"]
theorem representsComposite_of_isIso
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (h_comparison : IsIso (comparison N N')) :
    RepresentsComposite N N' (bimodule.{u, v} N N') := sorry

/-- Underived tensoring by `N` computes its total left-derived functor at every differential
graded homotopy object. -/
@[stacks 0BZ3 "everywhere-computing derived tensor model"]
abbrev ComputesEverywhere (N : DifferentialGradedBimodule.{u, v, v, v} A B) : Prop :=
  ∀ X : K R (DifferentialGradedModule.{u, v} A),
    Functor.LeftDerived.ComputesAt (derivedSourceFunctor.{u, v, v, v, v} N)
      (DifferentialGradedModule.quasiIso.{u, v, v} A) X

/-- Underived tensoring by `N'` computes its left-derived value on every object obtained by
underived tensoring with `N`. -/
@[stacks 0BZ3 "computation after derived tensoring"]
abbrev ComputesAfter
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C) : Prop :=
  ∀ X : K R (DifferentialGradedModule.{u, v} A),
    Functor.LeftDerived.ComputesAt (derivedSourceFunctor.{u, v, v, v, v} N')
      (DifferentialGradedModule.quasiIso.{u, v, v} B) ((dgFunctor N).mapK.obj X)

/-- A tensor model which computes its derived functor everywhere also computes after any
preceding tensor model. -/
@[stacks 0BZ3 "everywhere computation implies computation after tensoring"]
theorem ComputesEverywhere.computesAfter
    {N' : DifferentialGradedBimodule.{u, v, v, v} B C}
    (hN' : ComputesEverywhere N')
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) : ComputesAfter N N' := sorry

/-- If all three underived tensor functors compute their left-derived values at the relevant
objects, the explicit relative tensor bimodule represents the composite. This is the reusable
criterion for using `N ⊗_B N'` rather than an unspecified replacement bimodule. -/
@[stacks 0BZ3 "derived tensor composition comparison under computation hypotheses"]
theorem comparison_isIso_of_computesAt
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (hNComputes : ComputesEverywhere N)
    (hN'Computes : ComputesAfter N N')
    (hCompositeComputes : ComputesEverywhere (bimodule.{u, v} N N')) :
    IsIso (comparison N N') := sorry

/-- If the two tensor models and their explicit relative tensor composite compute everywhere,
then the derived composition comparison is invertible. -/
@[stacks 0BZ3 "derived tensor composition under everywhere computation"]
theorem comparison_isIso_of_computesEverywhere
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N' : DifferentialGradedBimodule.{u, v, v, v} B C)
    (hN : ComputesEverywhere N)
    (hN' : ComputesEverywhere N')
    (hComposite : ComputesEverywhere (bimodule.{u, v} N N')) :
    IsIso (comparison N N') := sorry

end DifferentialGradedBimodule.Tensor.Derived
