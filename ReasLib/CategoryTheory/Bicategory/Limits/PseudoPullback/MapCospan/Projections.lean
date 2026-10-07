module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Hom

/-!
# Projection comparisons for universal cospan maps

This module provides the first, second, and central-leg comparison isomorphisms for
`mapCospan`, including named forward and inverse formulas for each projection.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The universal map induced by a cospan transformation commutes with the first projection up
to the canonical lift comparison.
-/
noncomputable abbrev mapCospan.fstIso (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    mapCospan S T ψ ≫ T.fst ≅ S.fst ≫ ψ.left :=
  lift.fstIso (S.changeCospan ψ) T

/-- The forward first-projection comparison for `mapCospan` is the forward universal-lift
comparison.
-/
@[simp]
theorem mapCospan.fstIso.hom (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (mapCospan.fstIso S T ψ).hom =
      (lift.fstIso (S.changeCospan ψ) T).hom := sorry

/-- The inverse first-projection comparison for `mapCospan` is the inverse universal-lift
comparison.
-/
@[simp]
theorem mapCospan.fstIso.inv (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (mapCospan.fstIso S T ψ).inv =
      (lift.fstIso (S.changeCospan ψ) T).inv := sorry

/-- The universal map induced by a cospan transformation commutes with the second projection up
to the canonical lift comparison.
-/
noncomputable abbrev mapCospan.sndIso (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    mapCospan S T ψ ≫ T.snd ≅ S.snd ≫ ψ.right :=
  lift.sndIso (S.changeCospan ψ) T

/-- The forward second-projection comparison for `mapCospan` is the forward universal-lift
comparison.
-/
@[simp]
theorem mapCospan.sndIso.hom (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (mapCospan.sndIso S T ψ).hom =
      (lift.sndIso (S.changeCospan ψ) T).hom := sorry

/-- The inverse second-projection comparison for `mapCospan` is the inverse universal-lift
comparison.
-/
@[simp]
theorem mapCospan.sndIso.inv (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (mapCospan.sndIso S T ψ).inv =
      (lift.sndIso (S.changeCospan ψ) T).inv := sorry

/-- The universal map induced by a cospan transformation commutes with the central leg up to the
canonical lift comparison.
-/
noncomputable abbrev mapCospan.baseIso (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    mapCospan S T ψ ≫ (T.fst ≫ f') ≅
      (S.fst ≫ ψ.left) ≫ f' :=
  lift.baseIso (S.changeCospan ψ) T

/-- The forward central-leg comparison for `mapCospan` is the forward universal-lift comparison. -/
@[simp]
theorem mapCospan.baseIso.hom (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (mapCospan.baseIso S T ψ).hom =
      (lift.baseIso (S.changeCospan ψ) T).hom := sorry

/-- The inverse central-leg comparison for `mapCospan` is the inverse universal-lift comparison. -/
@[simp]
theorem mapCospan.baseIso.inv (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    (mapCospan.baseIso S T ψ).inv =
      (lift.baseIso (S.changeCospan ψ) T).inv := sorry

/-- The first-leg cell of the canonical changed-cospan cone morphism is the forward
first-projection comparison. -/
@[simp]
theorem mapCospan.hom.fstFac (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    fstFac (mapCospan.hom S T ψ) = (mapCospan.fstIso S T ψ).hom := sorry

/-- The second-leg cell of the canonical changed-cospan cone morphism is the forward
second-projection comparison. -/
@[simp]
theorem mapCospan.hom.sndFac (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    sndFac (mapCospan.hom S T ψ) = (mapCospan.sndIso S T ψ).hom := sorry

/-- The central cell of the canonical changed-cospan cone morphism is the forward central-leg
comparison. -/
@[simp]
theorem mapCospan.hom.baseFac (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    baseFac (mapCospan.hom S T ψ) = (mapCospan.baseIso S T ψ).hom := sorry

/-- In a locally groupoidal bicategory, the first-leg isomorphism of the canonical
changed-cospan cone morphism is `mapCospan.fstIso`. -/
@[simp]
theorem mapCospan.hom.fstIso [IsLocallyGroupoid B]
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    PseudoPullbackCone.fstIso (mapCospan.hom S T ψ) =
      mapCospan.fstIso S T ψ := sorry

/-- In a locally groupoidal bicategory, the second-leg isomorphism of the canonical
changed-cospan cone morphism is `mapCospan.sndIso`. -/
@[simp]
theorem mapCospan.hom.sndIso [IsLocallyGroupoid B]
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    PseudoPullbackCone.sndIso (mapCospan.hom S T ψ) =
      mapCospan.sndIso S T ψ := sorry

/-- In a locally groupoidal bicategory, the central isomorphism of the canonical changed-cospan
cone morphism is `mapCospan.baseIso`. -/
@[simp]
theorem mapCospan.hom.baseIso [IsLocallyGroupoid B]
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] :
    PseudoPullbackCone.baseIso (mapCospan.hom S T ψ) =
      mapCospan.baseIso S T ψ := sorry

end CategoryTheory.Bicategory.PseudoPullbackCone
