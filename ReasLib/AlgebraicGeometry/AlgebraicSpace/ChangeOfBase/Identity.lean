module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence

/-! # Identity change of base for algebraic spaces -/

@[expose] public section

-- Public constructions retain their private coordinate data in their explicit bodies.
set_option backward.privateInPublic true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite TypeCat
noncomputable section
universe u


namespace AlgebraicGeometry.AlgebraicSpace

/-- The identity-index isomorphism `Over.mk φ.left ≅ T` for a morphism to `Over.mk (𝟙 S)`. -/
private def extendBaseIdOverIso {S : Scheme.{u}} {T : Over S} (φ : T ⟶ Over.mk (𝟙 S)) :
    Over.mk φ.left ≅ T :=
  Over.isoMk (Iso.refl T.left) sorry

/-- The identity-index projection of a coproduct section of `j_!`. -/
private def extendBaseIdValue {S : Scheme.{u}} (F : AlgebraicSpace S) {T : (Over S)ᵒᵖ}
    (σ : (extendBasePresheaf (𝟙 S) F.functorOfPoints).obj T) :
    F.functorOfPoints.obj T :=
  F.functorOfPoints.map (extendBaseIdOverIso σ.1).inv.op σ.2

/-- The identity change-of-base of an algebraic space over `S` maps to the original space by
projecting the unique index `T ⟶ Over.mk (𝟙 S)`. -/
def extendBaseIdHom {S : Scheme.{u}} (F : AlgebraicSpace S) :
    extendBase (𝟙 S) F ⟶ F where
  app T := ofHom fun σ => extendBaseIdValue F σ
  naturality := fun _ _ _ => sorry

/-- `extendBaseIdHom` evaluates by transporting to the coproduct formula and applying the
identity-index projection. -/
theorem extendBaseIdHom_app {S : Scheme.{u}} (F : AlgebraicSpace S)
    (T : (Over S)ᵒᵖ) (σ : (extendBase (𝟙 S) F).functorOfPoints.obj T) :
    (extendBaseIdHom F).app T σ =
      extendBaseIdValue F σ := rfl

/-- The identity-index inclusion of a point of `F` into `extendBase (𝟙 S) F`. -/
private def extendBaseIdValueInv {S : Scheme.{u}} (F : AlgebraicSpace S) {T : (Over S)ᵒᵖ}
    (x : F.functorOfPoints.obj T) :
    (extendBasePresheaf (𝟙 S) F.functorOfPoints).obj T :=
  ⟨Over.homMk T.unop.hom (Category.comp_id T.unop.hom),
    F.functorOfPoints.map
      (extendBaseIdOverIso
        (Over.homMk T.unop.hom (Category.comp_id T.unop.hom))).hom.op x⟩

/-- The inverse identity-index inclusion of an algebraic space into its change-of-base along
`𝟙 S`. -/
def extendBaseIdInv {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F ⟶ extendBase (𝟙 S) F where
  app T := ofHom fun x => extendBaseIdValueInv F x
  naturality := fun _ _ _ => sorry

/-- `extendBaseIdHom` and `extendBaseIdInv` are inverse morphisms of algebraic spaces. -/
def extendBaseIdIso {S : Scheme.{u}} (F : AlgebraicSpace S) :
    extendBase (𝟙 S) F ≅ F where
  hom := extendBaseIdHom F
  inv := extendBaseIdInv F
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.AlgebraicSpace
