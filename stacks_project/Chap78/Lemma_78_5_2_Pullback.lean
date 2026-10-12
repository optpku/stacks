/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap78.Lemma_78_5_2_Over

/-!
# Monoidal structure of slice base change for algebraic spaces

Slice base change `overPullback f : Over B ⥤ Over B'` is monoidal with
respect to the Cartesian structures on the slices. The unit and tensorator
are built from `pullbackLift` and the Cartesian pairing, not from the
sorry-tainted chosen pullbacks of `HasPullbacks (AlgebraicSpace S)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pair `(f, 𝟙_{B'})` is a cone over `(𝟙_ (Over B)).hom` and `f`. -/
theorem overPullbackε_cone {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) :
    f ≫ (𝟙_ (Over B)).hom = (𝟙_ (Over B')).hom ≫ f := sorry

/-- The underlying map `B' ⟶ B ×_B B'` of the monoidal unit comparison. -/
def overPullbackεLeft {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B) :
    (𝟙_ (Over B')).left ⟶ ((overPullback f).obj (𝟙_ (Over B))).left :=
  pullbackLift (𝟙_ (Over B)).hom f f (𝟙_ (Over B')).hom (overPullbackε_cone f)

/-- The unit comparison of `overPullback f` commutes with the structure
morphisms to `B'`. -/
theorem overPullbackε_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) :
    overPullbackεLeft f ≫ ((overPullback f).obj (𝟙_ (Over B))).hom =
      (𝟙_ (Over B')).hom := sorry

/-- The monoidal unit isomorphism `𝟙_ (Over B') ≅ (overPullback f).obj (𝟙_ (Over B))`. -/
def overPullbackεIso {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B) :
    𝟙_ (Over B') ≅ (overPullback f).obj (𝟙_ (Over B)) :=
  Over.isoMk
    { hom := overPullbackεLeft f
      inv := (toUnit ((overPullback f).obj (𝟙_ (Over B)))).left
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (overPullbackε_w f)

/-- First projection of `X_{B'} ⊗ Y_{B'}` followed by `X_{B'} ⟶ X`. -/
def overPullbackμToLeft {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    ((overPullback f).obj X ⊗ (overPullback f).obj Y).left ⟶ X.left :=
  (fst ((overPullback f).obj X) ((overPullback f).obj Y)).left ≫ overPullbackFst f X

/-- Second projection of `X_{B'} ⊗ Y_{B'}` followed by `Y_{B'} ⟶ Y`. -/
def overPullbackμToRight {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    ((overPullback f).obj X ⊗ (overPullback f).obj Y).left ⟶ Y.left :=
  (snd ((overPullback f).obj X) ((overPullback f).obj Y)).left ≫ overPullbackFst f Y

/-- The first factor of the tensorator lands over `B`. -/
theorem overPullbackμToLeft_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    overPullbackμToLeft f X Y ≫ X.hom =
      ((overPullback f).obj X ⊗ (overPullback f).obj Y).hom ≫ f := sorry

/-- The second factor of the tensorator lands over `B`. -/
theorem overPullbackμToRight_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    overPullbackμToRight f X Y ≫ Y.hom =
      ((overPullback f).obj X ⊗ (overPullback f).obj Y).hom ≫ f := sorry

/-- The morphism `X_{B'} ×_{B'} Y_{B'} ⟶ X` over `B`. -/
def overPullbackμHomLeft {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    Over.mk (((overPullback f).obj X ⊗ (overPullback f).obj Y).hom ≫ f) ⟶ X :=
  Over.homMk (overPullbackμToLeft f X Y) (overPullbackμToLeft_w f X Y)

/-- The morphism `X_{B'} ×_{B'} Y_{B'} ⟶ Y` over `B`. -/
def overPullbackμHomRight {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    Over.mk (((overPullback f).obj X ⊗ (overPullback f).obj Y).hom ≫ f) ⟶ Y :=
  Over.homMk (overPullbackμToRight f X Y) (overPullbackμToRight_w f X Y)

/-- The underlying map `X_{B'} ×_{B'} Y_{B'} ⟶ X ×_B Y`. -/
def overPullbackμToTensor {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    ((overPullback f).obj X ⊗ (overPullback f).obj Y).left ⟶ (X ⊗ Y).left :=
  (lift (overPullbackμHomLeft f X Y) (overPullbackμHomRight f X Y)).left

/-- The pair `(overPullbackμToTensor, structure map to B')` is a cone over
`(X ⊗ Y).hom` and `f`. -/
theorem overPullbackμ_cone {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    overPullbackμToTensor f X Y ≫ (X ⊗ Y).hom =
      ((overPullback f).obj X ⊗ (overPullback f).obj Y).hom ≫ f := sorry

/-- The underlying map of the tensorator of `overPullback f`. -/
def overPullbackμLeft {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    ((overPullback f).obj X ⊗ (overPullback f).obj Y).left ⟶
      ((overPullback f).obj (X ⊗ Y)).left :=
  pullbackLift (X ⊗ Y).hom f (overPullbackμToTensor f X Y)
    ((overPullback f).obj X ⊗ (overPullback f).obj Y).hom
    (overPullbackμ_cone f X Y)

/-- The tensorator of `overPullback f` commutes with the structure morphisms
to `B'`. -/
theorem overPullbackμ_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    overPullbackμLeft f X Y ≫ ((overPullback f).obj (X ⊗ Y)).hom =
      ((overPullback f).obj X ⊗ (overPullback f).obj Y).hom := sorry

/-- The oplax comparison `(overPullback f).obj (X ⊗ Y) ⟶ X_{B'} ⊗ Y_{B'}`. -/
def overPullbackδ {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    (overPullback f).obj (X ⊗ Y) ⟶
      (overPullback f).obj X ⊗ (overPullback f).obj Y :=
  lift ((overPullback f).map (fst X Y)) ((overPullback f).map (snd X Y))

/-- The monoidal tensorator isomorphism of `overPullback f`. -/
def overPullbackμIso {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (X Y : Over B) :
    (overPullback f).obj X ⊗ (overPullback f).obj Y ≅
      (overPullback f).obj (X ⊗ Y) :=
  Over.isoMk
    { hom := overPullbackμLeft f X Y
      inv := (overPullbackδ f X Y).left
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (overPullbackμ_w f X Y)

/-- Slice base change along `f : B' ⟶ B` is monoidal on Cartesian slices. -/
noncomputable instance instMonoidal_overPullback {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (f : B' ⟶ B) : (overPullback f).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := overPullbackεIso f
      μIso := overPullbackμIso f
      μIso_hom_natural_left := sorry
      μIso_hom_natural_right := sorry
      associativity := sorry
      left_unitality := sorry
      right_unitality := sorry }

end AlgebraicGeometry.AlgebraicSpace
