module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Enriched

/-!
# Derived enriched representable functors for algebra-sheaf complexes

This leaf specializes the coefficient-generic enriched representable construction to the
canonical derived category of modules over a sheaf of commutative `R`-algebras.  It owns the
right-derived functor with its `endDGA K`-module structure and its comparison unit.  Constructing
the tensor-representable adjunction additionally uses the sectionwise currying equivalence owned by
the sibling `TensorWithObject.Adjunction` leaf; the derived adjunction itself is exported by
`TensorWithObject.Derived.Adjunction`.
-/

@[expose] public section

noncomputable section

universe r u v w z g

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived

-- Use the existing standard localization for the actual underlying ring-sheaf carrier.
attribute [local instance] RingedSite.Hom.RingPresentation.moduleHasDerivedCategory

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Quasi-isomorphisms in the enriched homotopy category of `O`-module complexes. -/
@[stacks 09LY "arbitrary-ring representable denominators"]
abbrev representableQis :
    MorphismProperty (DifferentialGradedCategory.K R
      (Complex.{r, u, v, w, max u z} O)) :=
  CategoryTheory.CochainComplex.Enriched.Over.quasiIso
    (R := R) (A := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)

/-- The existence condition for the coefficient-generic derived enriched representable functor. -/
@[stacks 09LY "existence of the arbitrary-ring derived representable functor"]
abbrev HasRepresentable (K : Complex.{r, u, v, w, max u z} O) : Prop :=
  DifferentialGradedCategory.Representable.HasUnderlyingDerivedFunctor
    K (representableQis (O := O))

/-- K-injective resolutions make the underlying enriched representable source right derivable.
The resulting enriched functor retains the canonical `endDGA K`-action. -/
@[stacks 09LY "arbitrary-ring derived representable definedness"]
instance hasRepresentable_of_isGrothendieck
    [IsGrothendieckAbelian.{g}
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)]
    (K : Complex.{r, u, v, w, max u z} O) :
    HasRepresentable K := sorry

/-- The total right-derived enriched representable functor `RHom(K, -)`, retaining its
right-module structure over `endDGA K`. -/
@[stacks 09LY "arbitrary-ring derived enriched representable functor"]
noncomputable abbrev representableFunctor
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    DerivedCategory
        (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O) ⥤
      DifferentialGradedModule.Derived.Category (endDGA K) :=
  DifferentialGradedCategory.Representable.derivedFunctor K
    (SheafOfModules.CommAlg.Derived.Q O) (representableQis (O := O))

/-- The coefficient-generic derived representable functor is additive. -/
@[stacks 09LY "additivity of the arbitrary-ring derived representable functor"]
noncomputable instance representableFunctor_additive
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K).Additive := sorry

/-- The coefficient-generic derived representable functor is linear over the coefficient ring. -/
@[stacks 09LY "linearity of the arbitrary-ring derived representable functor"]
noncomputable instance representableFunctor_linear
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K).Linear R := sorry

/-- The canonical comparison from homotopy-level enriched representable Hom to
`representableFunctor K`. -/
@[stacks 09LY "arbitrary-ring derived representable unit"]
noncomputable abbrev representableUnit
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    DifferentialGradedCategory.Representable.sourceFunctor K ⟶
      SheafOfModules.CommAlg.Derived.Q O ⋙ representableFunctor K :=
  DifferentialGradedCategory.Representable.derivedUnit K
    (SheafOfModules.CommAlg.Derived.Q O) (representableQis (O := O))

/-- The exact right-derived endpoint used by the tensor-representable adjunction.

The generic representable instance proves the same proposition, but naming this specialization
prevents composition instances in adjunction construction from recursively searching through a
larger right-derived functor expression. -/
@[stacks 09LY "right-derived endpoint for the arbitrary-ring representable functor"]
instance representableFunctor_isRightDerived
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K).IsRightDerivedFunctor
      (representableUnit K) (representableQis (O := O)) := sorry

/-- The comparison unit after forgetting the `endDGA K`-module structure. -/
@[stacks 09LY "underlying arbitrary-ring derived representable unit"]
noncomputable abbrev representableForgetUnit
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    DifferentialGradedCategory.Representable.underlyingSourceFunctor K ⟶
      SheafOfModules.CommAlg.Derived.Q O ⋙
        (representableFunctor K ⋙
          DifferentialGradedModule.Derived.forget (endDGA K)) :=
  DifferentialGradedCategory.Representable.derivedForgetUnit K
    (SheafOfModules.CommAlg.Derived.Q O) (representableQis (O := O))

/-- Forgetting the endomorphism-DGA action preserves the exact right-derived endpoint. -/
@[stacks 09LY "right-derived endpoint after forgetting the representable action"]
instance representableForget_isRightDerived
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    (representableFunctor K ⋙
      DifferentialGradedModule.Derived.forget (endDGA K)).IsRightDerivedFunctor
        (representableForgetUnit K) (representableQis (O := O)) := sorry

/-- Forgetting the `endDGA K`-action identifies the enriched representable functor with the
ordinary total right-derived representable source. -/
@[stacks 09LY "underlying arbitrary-ring derived representable comparison"]
noncomputable abbrev representableForgetIso
    (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K] :
    representableFunctor K ⋙
        DifferentialGradedModule.Derived.forget (endDGA K) ≅
      (DifferentialGradedCategory.Representable.underlyingSourceFunctor K).totalRightDerived
        (SheafOfModules.CommAlg.Derived.Q O) (representableQis (O := O)) :=
  DifferentialGradedCategory.Representable.derivedForgetIso K
    (SheafOfModules.CommAlg.Derived.Q O) (representableQis (O := O))

section Checks

variable (K : Complex.{r, u, v, w, max u z} O) [HasRepresentable K]

#synth (representableFunctor K).Additive
#synth (representableFunctor K).Linear R
#synth (representableFunctor K).IsRightDerivedFunctor
  (representableUnit K) (representableQis (O := O))
#synth (representableFunctor K ⋙ DifferentialGradedModule.Derived.forget (endDGA K)).Additive
#synth Functor.Linear R
  (representableFunctor K ⋙ DifferentialGradedModule.Derived.forget (endDGA K))
#synth (representableFunctor K ⋙
  DifferentialGradedModule.Derived.forget (endDGA K)).IsRightDerivedFunctor
    (representableForgetUnit K) (representableQis (O := O))

end Checks

end SheafOfModules.CommAlg.TensorWithObject.Derived
