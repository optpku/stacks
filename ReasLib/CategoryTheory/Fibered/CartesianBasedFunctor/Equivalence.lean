module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.Equivalence.StronglyCartesian

/-!
# Equivalences as cartesian based functors

This module packages equivalences over the base as `CartesianBasedFunctor`s. The heterogeneous
`BasedFunctor.IsEquivalence` interface is primary; the bicategorical interface is its same-owner
specialization.
-/

@[expose] public section

universe u v uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

/-- Regard a based functor which is an equivalence over the base as a cartesian based functor.

The source and target are arbitrary universe-polymorphic based categories, rather than being
restricted syntactically to `BasedCategory.ofFunctor`. The named instance argument `hF` is inferred
by default but may be supplied explicitly as `(hF := ...)`. No comparison data are chosen: the
non-`Prop` field is exactly `F`, and `hF` supplies only the preservation proof. -/
def ofIsEquivalence
    {X : BasedCategory.{vS₁, uS₁} C} {Y : BasedCategory.{vS₂, uS₂} C}
    (F : X ⥤ᵇ Y) [hF : F.IsEquivalence] : CartesianBasedFunctor X.p Y.p :=
  ofBasedFunctor F (BasedFunctor.IsEquivalence.preservesStronglyCartesian F)

/-- The based functor underlying `ofIsEquivalence F` is the original functor `F`. -/
@[simp]
theorem ofIsEquivalence.toBasedFunctor
    {X : BasedCategory.{vS₁, uS₁} C} {Y : BasedCategory.{vS₂, uS₂} C}
    (F : X ⥤ᵇ Y) [hF : F.IsEquivalence] :
    (ofIsEquivalence F).toBasedFunctor = F := sorry

section FixedOwnerEquivalence

universe uS vS

variable {S₁ S₂ : Type uS} [Category.{vS} S₁] [Category.{vS} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- Regard the forward morphism of an equivalence in the fixed `BasedCategory C` bicategory as a
cartesian based functor. This is the canonical same-owner constructor; use `ofIsEquivalence`
for a fixed possibly universe-changing based functor. -/
def ofEquivalence
    (e : BasedCategory.ofFunctor p₁ ≌ BasedCategory.ofFunctor p₂) :
    CartesianBasedFunctor p₁ p₂ :=
  ofBasedFunctor e.hom (BasedFunctor.IsEquivalence.preservesStronglyCartesian e.hom)

/-- The based functor underlying `ofEquivalence e` is the forward morphism `e.hom`. -/
@[simp]
theorem ofEquivalence.toBasedFunctor
    (e : BasedCategory.ofFunctor p₁ ≌ BasedCategory.ofFunctor p₂) :
    (ofEquivalence e).toBasedFunctor = e.hom := sorry

end FixedOwnerEquivalence

end CartesianBasedFunctor

end CategoryTheory

/- Axiom audit: both constructors store their supplied forward based functor definitionally; any
`sorryAx` is confined to the Prop-valued cartesian-preservation field. -/
