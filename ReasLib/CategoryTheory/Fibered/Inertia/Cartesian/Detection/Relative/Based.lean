/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Relative.Underlying

/-!
# Based cartesian closure for relative inertia

This leaf owns the preservation statements for based forgetful, identity-section, square-map,
and relative-to-absolute actions. Their generic detection criteria are in `Underlying`.
-/

@[expose] public section

universe u v uS vS uT vT w
universe u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂'

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace BasedCategory.RelativeInertia

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vS, uS} C}
variable {Y : BasedCategory.{vT, uT} C}

namespace Detection.StronglyCartesian

/-- For a cartesian based functor with fibred source, strong cartesianness in based relative
inertia is detected by the underlying source arrow. -/
@[stacks 04Z4 "relative inertia strong-cartesian detection"]
theorem iffForget
    [X.p.IsFibered] (F : X ⥤ᵇ Y) (hF : F.PreservesStronglyCartesian)
    {A B : (relativeInertia F).obj} {R Q : C} {f : R ⟶ Q} {φ : A ⟶ B} :
    (relativeInertia F).p.IsStronglyCartesian f φ ↔
      X.p.IsStronglyCartesian f (CategoryTheory.RelativeInertia.hom φ) := sorry

end Detection.StronglyCartesian

/-- Forgetting a relative-inertia automorphism preserves strongly cartesian arrows when the
source projection is fibred and the defining based functor is cartesian. -/
@[stacks 042H "relative inertia forgetful cartesian preservation"]
theorem forget.preservesStronglyCartesian
    [X.p.IsFibered] (F : X ⥤ᵇ Y) (hF : F.PreservesStronglyCartesian) :
    (BasedCategory.RelativeInertia.forget F).PreservesStronglyCartesian := sorry

/-- The relative identity-automorphism section preserves strongly cartesian arrows without any
fibredness assumption. -/
@[stacks 04Z3 "relative inertia identity-section cartesian preservation"]
theorem identitySection.preservesStronglyCartesian (F : X ⥤ᵇ Y) :
    (BasedCategory.RelativeInertia.identitySection F).PreservesStronglyCartesian := sorry

/-- A cartesian invertible square induces a strongly-cartesian-preserving based map on relative
inertia. Only cartesianness of the source horizontal map and source-side vertical map is needed. -/
@[stacks 04Z4 "relative inertia square cartesian preservation"]
theorem map.preservesStronglyCartesian
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}
    [S₁.p.IsFibered]
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (hF₁ : F₁.PreservesStronglyCartesian)
    (hG : G.PreservesStronglyCartesian) :
    (BasedCategory.RelativeInertia.map G G' comm).PreservesStronglyCartesian := sorry

/-- Forgetting the relative kernel condition preserves strongly cartesian arrows when the source
projection is fibred and the defining based functor is cartesian. -/
@[stacks 04Z5 "relative-to-absolute cartesian preservation"]
theorem toInertia.preservesStronglyCartesian
    [X.p.IsFibered] (F : X ⥤ᵇ Y) (hF : F.PreservesStronglyCartesian) :
    (BasedCategory.RelativeInertia.toInertia F).PreservesStronglyCartesian := sorry

end BasedCategory.RelativeInertia

end CategoryTheory
