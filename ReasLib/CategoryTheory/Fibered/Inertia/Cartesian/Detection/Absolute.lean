module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Relative

/-!
# Cartesian detection for absolute inertia

Lift equations and strong cartesianness in based absolute inertia are detected by
the underlying total-category arrow. These criteria supply preservation for the
forgetful functor, identity section, and absolute-inertia map.
-/

@[expose] public section

universe u v uS vS uT vT

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace BasedCategory.Inertia

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vS, uS} C}
variable {Y : BasedCategory.{vT, uT} C}

namespace Detection

namespace HomLift

/-- Lift equations in based absolute inertia are detected by the forgetful underlying arrow. -/
@[stacks 04Z4 "absolute inertia lift detection"]
theorem iffForget
    {A B : (BasedCategory.inertia X).obj}
    {R Q : C} {f : R ⟶ Q} {φ : A ⟶ B} :
    (BasedCategory.inertia X).p.IsHomLift f φ ↔
      X.p.IsHomLift f (RelativeInertia.hom φ) := sorry
/- Proof strategy: rewrite the absolute-inertia projection with `BasedCategory.inertia_p` and
apply `RelativeInertia.Detection.HomLift.iffProjection`. -/

end HomLift

namespace StronglyCartesian

/-- Strong cartesianness in based absolute inertia is detected by the forgetful underlying arrow. -/
@[stacks 04Z4 "absolute inertia strong-cartesian detection"]
theorem iffForget
    [X.p.IsFibered] {A B : (BasedCategory.inertia X).obj}
    {R Q : C} {f : R ⟶ Q} {φ : A ⟶ B} :
    (BasedCategory.inertia X).p.IsStronglyCartesian f φ ↔
      X.p.IsStronglyCartesian f (RelativeInertia.hom φ) := sorry
/- Proof strategy: rewrite with `BasedCategory.inertia_p` and apply
`RelativeInertia.Detection.StronglyCartesian.projectionSelf.iff`. -/

end StronglyCartesian

end Detection

/-- Forgetting an absolute-inertia automorphism preserves strongly cartesian morphisms. -/
@[stacks 042H "absolute inertia forgetful cartesian preservation"]
theorem forget.preservesStronglyCartesian
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered] :
    (BasedCategory.Inertia.forget X).PreservesStronglyCartesian := sorry
/- Proof strategy: use `Detection.StronglyCartesian.iffForget` in the reflecting direction and the
computation theorem for `Inertia.forget`. -/

/-- The identity-automorphism section preserves strongly cartesian morphisms. -/
@[stacks 04Z3 "absolute inertia identity-section cartesian preservation"]
theorem identitySection.preservesStronglyCartesian
    (X : BasedCategory.{vS, uS} C) :
    (BasedCategory.Inertia.identitySection X).PreservesStronglyCartesian := sorry
/- Proof strategy: the section does not change the underlying arrow; apply
`Detection.StronglyCartesian.iffForget` in the lifting direction. -/

/-- A strongly-cartesian-preserving based functor induces a strongly-cartesian-preserving map on
absolute inertia. -/
@[stacks 04Z4 "absolute inertia map cartesian preservation"]
theorem map.preservesStronglyCartesian
    [X.p.IsFibered]
    (G : X ⥤ᵇ Y) (hG : G.PreservesStronglyCartesian) :
    (BasedCategory.Inertia.map G).PreservesStronglyCartesian := sorry
/- Proof strategy: reflect the source inertia hypothesis with
`Detection.StronglyCartesian.iffForget`, apply `hG`, rewrite the underlying mapped arrow with
`RelativeInertia.map.hom`, and lift the result with the target detection theorem. -/

end BasedCategory.Inertia

end CategoryTheory
