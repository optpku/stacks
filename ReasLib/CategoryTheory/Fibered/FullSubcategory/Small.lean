module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Representatives
public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.Over

/-!
# Small full-subcategory models of stacks

Fiberwise essential smallness can be assembled into one small full subcategory of the total
category. This file records the selected full-subcategory model without exposing a retraction
that chooses a representative for every ambient object or rebuilding the fiberwise closure
proof at each application.
-/

@[expose] public section

universe uC vC uS vS wD

namespace CategoryTheory

open scoped Bicategory

open scoped BasedFunctor

variable {C : Type uC} {S : Type uS}
variable [Category.{vC} C] [Category.{vS} S]

namespace StackOver

variable {J : GrothendieckTopology C}

/-- A small full-subcategory model of a bundled stack. It records a small object property on
the given stack, the stack condition on the restricted projection, and essential surjectivity
of the inclusion. -/
@[stacks 03ZZ "small full-subcategory model"]
structure SmallModel (X : StackOver.{uC, vC, uS, vS} J) where
  /-- The object property selecting the small full subcategory. -/
  property : ObjectProperty X.total
  /-- The selected full subcategory is small. -/
  small : ObjectProperty.Small.{wD} property
  /-- The restricted projection remains a stack. -/
  isStackOnSite : IsStack.OnSite J (property.ι ⋙ X.p)
  /-- Every object of the ambient stack is isomorphic to a selected object. -/
  essSurj : property.ι.EssSurj

namespace SmallModel

variable {X : StackOver.{uC, vC, uS, vS} J}

/-- The selected objects of a small stack model form a small type in the model universe. -/
instance propertySmall (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    ObjectProperty.Small.{wD} M.property := sorry

/-- The restricted projection of a small stack model is canonically a stack. -/
@[stacks 03ZZ "small-model restricted stack instance"]
instance stackOnSite (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    IsStack.OnSite J (M.property.ι ⋙ X.p) := sorry

/-- The inclusion of a small stack model is canonically essentially surjective. -/
@[stacks 03ZZ "small-model inclusion essential surjectivity"]
instance inclusionEssSurj (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    M.property.ι.EssSurj := sorry

/-- The inclusion of a small stack model is an equivalence of total categories. -/
@[stacks 03ZZ "small-model inclusion equivalence instance"]
instance inclusionIsEquivalence (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    M.property.ι.IsEquivalence := sorry

/-- The restricted projection bundled as the source stack of the small model. -/
@[stacks 03ZZ "small-model source stack"]
noncomputable def source
    (M : SmallModel.{uC, vC, uS, vS, wD} X) : StackOver J :=
  StackOver.mk
    (FiberedCategoryOver.ofFunctor (M.property.ι ⋙ X.p)) M.isStackOnSite

namespace source

/-- The source projection is the restriction of the original stack projection to the selected
full subcategory. -/
@[simp, stacks 03ZZ "small-model source projection readout"]
theorem p (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    M.source.p = M.property.ι ⋙ X.p := sorry

/-- The total category of the source stack is the selected full subcategory. -/
@[simp, stacks 03ZZ "small-model source total-category readout"]
theorem total (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    M.source.total = M.property.FullSubcategory := sorry

end source

/-- The total category of the source stack is small in the model universe. -/
@[stacks 03ZZ "small-model source smallness"]
instance sourceSmall (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    Small.{wD} M.source.total := sorry

/-- The full-subcategory inclusion as a based functor into the original bundled stack. -/
@[stacks 03ZZ "small-model based inclusion"]
def inclusionBased
    (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    BasedFunctor M.source.toBasedCategory X.toBasedCategory where
  toFunctor := M.property.ι
  w := rfl

namespace inclusionBased

/-- The based inclusion of a small stack model preserves strongly cartesian morphisms. -/
@[stacks 03ZZ "small-model inclusion cartesian preservation"]
theorem preservesStronglyCartesian
    (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    M.inclusionBased.PreservesStronglyCartesian := sorry

end inclusionBased

/-- The small full-subcategory inclusion as a morphism into the original bundled stack. -/
@[stacks 03ZZ "small-model inclusion"]
noncomputable def inclusion
    (M : SmallModel.{uC, vC, uS, vS, wD} X) : M.source ⟶ X :=
  StackOver.Hom.ofBasedFunctor M.inclusionBased
    (inclusionBased.preservesStronglyCartesian M)

namespace inclusion

/-- The based functor underlying the small-model inclusion is the literal full-subcategory
inclusion. -/
@[simp, stacks 03ZZ "small-model based-inclusion readout"]
theorem toBasedFunctor
    (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    StackOver.Hom.toBasedFunctor M.inclusion = M.inclusionBased := sorry

/-- The total functor underlying the small-model inclusion is the literal full-subcategory
inclusion. -/
@[simp, stacks 03ZZ "small-model total-inclusion readout"]
theorem toFunctor
    (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    StackOver.Hom.toFunctor M.inclusion = M.property.ι := sorry

/-- The small-model inclusion is an equivalence over the base category. -/
@[stacks 03ZZ "stack inclusion equivalence"]
theorem isEquivalence
    (M : SmallModel.{uC, vC, uS, vS, wD} X) :
    StackOver.Hom.IsEquivalence M.inclusion := sorry

end inclusion

/-- A bundled stack with essentially small fibers admits a small, essentially surjective
full-subcategory model. -/
@[stacks 03ZZ]
theorem nonemptyOfEssentiallySmall
    (X : StackOver.{uC, vC, uS, vS} J) [Small.{wD} C]
    (h : ∀ U : C,
      ObjectProperty.EssentiallySmall.{wD}
        (⊤ : ObjectProperty (X.p.Fiber U))) :
    Nonempty (SmallModel.{uC, vC, uS, vS, wD} X) := sorry

/-- Projection-level companion to `nonemptyOfEssentiallySmall`, for a stack supplied as a
functor with a stack instance. -/
@[stacks 03ZZ "projection-level small stack model"]
theorem nonemptyOfProjection
    (J : GrothendieckTopology C) (p : S ⥤ C)
    [Small.{wD} C] [IsStack.OnSite J p]
    (h : ∀ U : C,
      ObjectProperty.EssentiallySmall.{wD}
        (⊤ : ObjectProperty (p.Fiber U))) :
    Nonempty
      (SmallModel.{uC, vC, uS, vS, wD}
        (StackOver.ofProjection J p)) := sorry

/- Data audit: `SmallModel` stores the source-facing object property explicitly. `source` is the
corresponding full-subcategory projection, with its total category and projection exposed by
`source.total` and `source.p`; `inclusionBased` stores the literal inclusion functor, and
`inclusion.isEquivalence` records the choice-free equivalence property. No inverse functor is
packaged here because `SmallModel` does not select a representative for each ambient object.
Deferred content is confined to stack, smallness, cartesian-preservation,
essential-surjectivity, and equivalence-property proofs. -/

end SmallModel

end StackOver

end CategoryTheory
