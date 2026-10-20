module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Basic

/-!
# Endpoint projections for adjoint factorization

The intermediate vertical-comma category has canonical source and target legs.
This leaf owns their fibredness and objectwise computation rules.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open scoped Bicategory

universe u v w

namespace CategoryTheory.FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, w} C}

noncomputable section

namespace AdjointFactorization

/-- The right endpoint projection `VerticalComma F ⥤ X.total`. -/
private def toSourceFunctor (F : X ⟶ Y) : VerticalComma F ⥤ X.total :=
  (verticalArrowProperty F).ι ⋙ Comma.snd _ _

/-- The right endpoint projection is a functor over `C`. -/
private theorem toSourceFunctorComm (F : X ⟶ Y) :
    toSourceFunctor F ⋙ X.p = projection F := sorry
/- Proof strategy: apply `Functor.ext`. On objects, combine `Functor.congr_obj (comm F)` with
`IsHomLift.codomain_eq`. On morphisms, map the comma square by `Y.p` and use `IsHomLift.fac'`
for its two vertical comparison arrows. -/

/-- The left endpoint projection `VerticalComma F ⥤ Y.total`. -/
private def toTargetFunctor (F : X ⟶ Y) : VerticalComma F ⥤ Y.total :=
  (verticalArrowProperty F).ι ⋙ Comma.fst _ _

/-- The left endpoint projection is a functor over `C`. -/
private theorem toTargetFunctorComm (F : X ⟶ Y) :
    toTargetFunctor F ⋙ Y.p = projection F := sorry
/- Proof strategy: unfold `toTargetFunctor` and `projection`; both sides normalize to the
composite of the full-subcategory inclusion, `Comma.fst`, and `Y.p`. -/

/-- The right endpoint projection preserves strongly cartesian arrows. -/
private theorem toSourcePreservesStronglyCartesian (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      ({ toFunctor := toSourceFunctor F
         w := toSourceFunctorComm F } :
        (middle F).toBasedCategory ⥤ᵇ X.toBasedCategory) := sorry
/- Proof strategy: compare a strongly cartesian comma morphism with the canonical pullback used
in `projectionIsFibered`. The vertical comparison isomorphism has an isomorphism as its right
component; transport strong cartesianness across it and use uniqueness of cartesian lifts. -/

/-- The projection from the intermediate fibred category back to `X`. -/
def toSource (F : X ⟶ Y) : middle F ⟶ X :=
  ofBasedFunctor
    ({ toFunctor := toSourceFunctor F
       w := toSourceFunctorComm F } :
      (middle F).toBasedCategory ⥤ᵇ X.toBasedCategory)
    (toSourcePreservesStronglyCartesian F)

/-- `toSource F` sends a vertical arrow to its source-side endpoint. -/
@[simp]
theorem toSource_obj (F : X ⟶ Y) (P : VerticalComma F) :
    (toFunctor (toSource F)).obj P = P.obj.right := sorry
/- Proof strategy: unfold only the public constructors `toSource` and `toFunctor`, then reduce the
full-subcategory inclusion followed by `Comma.snd` using its object projection formula. -/

/-- `toSource F` sends a vertical comma square to its source-side component. -/
@[simp]
theorem toSource_map (F : X ⟶ Y) {P Q : VerticalComma F} (φ : P ⟶ Q) :
    (toFunctor (toSource F)).map φ = φ.hom.right := sorry
/- Proof strategy: unfold only the public constructors `toSource` and `toFunctor`, then reduce the
full-subcategory inclusion followed by `Comma.snd` using its map projection formula. -/

/-- The left endpoint projection preserves strongly cartesian arrows. -/
private theorem toTargetPreservesStronglyCartesian (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      ({ toFunctor := toTargetFunctor F
         w := toTargetFunctorComm F } :
        (middle F).toBasedCategory ⥤ᵇ Y.toBasedCategory) := sorry
/- Proof strategy: use the same canonical pullback comparison as in
`toSourcePreservesStronglyCartesian`, take its left component in `Y`, and transport the chosen
target cartesian lift across the resulting vertical isomorphism. -/

/-- The projection from the intermediate fibred category to `Y`. -/
def toTarget (F : X ⟶ Y) : middle F ⟶ Y :=
  ofBasedFunctor
    ({ toFunctor := toTargetFunctor F
       w := toTargetFunctorComm F } :
      (middle F).toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (toTargetPreservesStronglyCartesian F)

/-- `toTarget F` sends a vertical arrow to its target-side endpoint. -/
@[simp]
theorem toTarget_obj (F : X ⟶ Y) (P : VerticalComma F) :
    (toFunctor (toTarget F)).obj P = P.obj.left := sorry
/- Proof strategy: unfold only the public constructors `toTarget` and `toFunctor`, then reduce the
full-subcategory inclusion followed by `Comma.fst` using its object projection formula. -/

/-- `toTarget F` sends a vertical comma square to its target-side component. -/
@[simp]
theorem toTarget_map (F : X ⟶ Y) {P Q : VerticalComma F} (φ : P ⟶ Q) :
    (toFunctor (toTarget F)).map φ = φ.hom.left := sorry
/- Proof strategy: unfold only the public constructors `toTarget` and `toFunctor`, then reduce the
full-subcategory inclusion followed by `Comma.fst` using its map projection formula. -/

/-- The target leg of the canonical factorization is a fibred functor. -/
@[instance]
theorem toTargetIsFibered (F : X ⟶ Y) :
    (toFunctor (toTarget F)).IsFibered := sorry
/- Proof strategy: apply `Functor.IsFibered.of_exists_isStronglyCartesian`. Pull back the left
endpoint in `Y` and the right endpoint in `X` over the same base arrow, lift the vertical
comparison through the source pullback, and use the componentwise cartesian universal properties. -/

end AdjointFactorization

end

end CategoryTheory.FiberedCategoryOver
