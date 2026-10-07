module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap79.Lemma_79_12_2_FinitePart

/-!
# Covariance of the finite-part sheaf along open immersions

An open immersion `j : X' ⟶ X` over `Y` induces a canonical map of finite-part
sheaves sending a pair `(a, Z)` to `(a, j(Z))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePart.Point

/-- The identity square on the `T`-leg used to push a finite-part pair along an
open immersion over `Y`. -/
theorem mapHom_w₁ {S : Scheme.{u}} {Y : AlgebraicSpace S} {T : Over S}
    (a : ofOver T ⟶ Y) : a ≫ 𝟙 Y = 𝟙 (ofOver T) ≫ a := sorry

/-- The commutative triangle `j ≫ f = f'` as a square on the `X`-leg. -/
theorem mapHom_w₂ {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) (hcomm : j ≫ f = f') :
    f' ≫ 𝟙 Y = j ≫ f := sorry

/-- The comparison `T ×_Y X' ⟶ T ×_Y X` induced by an open immersion `j` over `Y`. -/
def mapHom {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) (hcomm : j ≫ f = f') {T : Over S} (a : ofOver T ⟶ Y) :
    pullback a f' ⟶ pullback a f :=
  pullback.map a f' a f (𝟙 (ofOver T)) j (𝟙 Y) (mapHom_w₁ a) (mapHom_w₂ j hcomm)

/-- `mapHom` is the `pullback.map` comparison induced by `j` over `Y`. -/
theorem mapHom_eq {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) (hcomm : j ≫ f = f') {T : Over S} (a : ofOver T ⟶ Y) :
    mapHom j hcomm a =
      pullback.map a f' a f (𝟙 (ofOver T)) j (𝟙 Y) (mapHom_w₁ a) (mapHom_w₂ j hcomm) :=
  sorry

/-- Pushing a finite-part pair along an open immersion `j` over `Y` sends `(a, Z)`
to `(a, j(Z))`. -/
def map {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f') {T : Over S}
    (p : Point f' T) : Point f T where
  a := p.a
  Z :=
    { carrier := Points.map (mapHom j hcomm p.a) '' p.Z
      is_open' := sorry }
  isFinite := sorry

/-- `FinitePart.Point.map` preserves the morphism to `Y`. -/
theorem map_a {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f') {T : Over S}
    (p : Point f' T) : (map j hcomm p).a = p.a := sorry

end FinitePart.Point

/-- The canonical map of finite-part sheaves induced by an open immersion over `Y`. -/
def finitePartOpenMap {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') :
    finitePartSheaf f' ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : FinitePart.Point f' T.unop) ↦
        FinitePart.Point.map j hcomm p
      naturality := sorry }

/-- Components of `finitePartOpenMap` are `FinitePart.Point.map` on opposite sections. -/
theorem finitePartOpenMap_app {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') (T : (Over S)ᵒᵖ) :
    (finitePartOpenMap j hcomm).hom.app T =
      TypeCat.ofHom fun (p : FinitePart.Point f' T.unop) ↦
        FinitePart.Point.map j hcomm p := sorry

/-- On a pair `(a, Z)` over `T`, `finitePartOpenMap` acts by `(a, Z) ↦ (a, j(Z))`. -/
theorem finitePartOpenMap_pair {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') {T : Over S} (p : FinitePart.Point f' T) :
    (finitePartOpenMap j hcomm).hom.app (op T) p = FinitePart.Point.map j hcomm p := sorry

end AlgebraicGeometry.AlgebraicSpace

