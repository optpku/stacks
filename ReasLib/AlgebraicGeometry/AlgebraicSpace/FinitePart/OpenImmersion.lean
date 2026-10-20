module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! # Covariance of finite-part sheaves along open immersions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePart.Point

/-- A morphism over the target induces the comparison of fibre products with a test scheme. -/
def mapHom {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) (hcomm : j ≫ f = f') {T : Over S} (a : ofOver T ⟶ Y) :
    pullback a f' ⟶ pullback a f :=
  pullback.lift (pullback.fst a f') (pullback.snd a f' ≫ j) (by
    rw [Category.assoc, hcomm]
    exact pullback.condition)

/-- The comparison of fibre products preserves the first projection. -/
theorem mapHom_fst {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) (hcomm : j ≫ f = f') {T : Over S} (a : ofOver T ⟶ Y) :
    mapHom j hcomm a ≫ pullback.fst a f = pullback.fst a f' := by
  apply pullback.lift_fst

/-- The second projection of the comparison is the original projection followed by the given morphism. -/
theorem mapHom_snd {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) (hcomm : j ≫ f = f') {T : Over S} (a : ofOver T ⟶ Y) :
    mapHom j hcomm a ≫ pullback.snd a f = pullback.snd a f' ≫ j := by
  apply pullback.lift_snd

/-- The image of the open of a finite-part pair under an open immersion is open. -/
theorem map_isOpen {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f')
    {T : Over S} (p : Point f' T) :
    IsOpen (Points.map (mapHom j hcomm p.a) '' p.Z) := sorry

/-- The image open of a finite-part pair under an open immersion is finite over the test scheme. -/
theorem map_isFinite {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f')
    {T : Over S} (p : Point f' T) :
    IsFinite ((OpenSubspace.fromOpens
      ⟨Points.map (mapHom j hcomm p.a) '' p.Z, map_isOpen j hcomm p⟩).ι ≫
        pullback.fst p.a f) := sorry

/-- Direct image along an open immersion sends a finite-part pair to its image pair. -/
def map {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f') {T : Over S}
    (p : Point f' T) : Point f T where
  a := p.a
  Z := ⟨Points.map (mapHom j hcomm p.a) '' p.Z, map_isOpen j hcomm p⟩
  isFinite := map_isFinite j hcomm p

/-- Direct image of a finite-part pair preserves its morphism to the target. -/
theorem map_a {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f') {T : Over S}
    (p : Point f' T) : (map j hcomm p).a = p.a := rfl

/-- The open carrier of the image pair is the direct image of the original open carrier. -/
theorem map_Z {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f') {T : Over S}
    (p : Point f' T) :
    (map j hcomm p).Z.carrier =
      Points.map (mapHom j hcomm p.a) '' p.Z := rfl

/-- Direct image of finite-part pairs along an open immersion commutes with restriction. -/
theorem map_restrict {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y}
    {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f')
    {T T' : Over S} (p : Point f' T) (h : T' ⟶ T) :
    (map j hcomm p).restrict h = map j hcomm (p.restrict h) := sorry

end FinitePart.Point

/-- An open immersion over the target induces the direct-image morphism of finite-part sheaves. -/
def finitePartOpenMap {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') :
    finitePartSheaf f' ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : FinitePart.Point f' T.unop) ↦
        FinitePart.Point.map j hcomm p
      naturality := by
        intro T T' h
        apply ConcreteCategory.hom_ext
        intro p
        exact (FinitePart.Point.map_restrict j hcomm p h.unop).symm }

/-- Components of the direct-image sheaf morphism are the direct-image maps on pairs. -/
theorem finitePartOpenMap_app {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') (T : (Over S)ᵒᵖ) :
    (finitePartOpenMap j hcomm).hom.app T =
      TypeCat.ofHom fun (p : FinitePart.Point f' T.unop) ↦
        FinitePart.Point.map j hcomm p := rfl

/-- The direct-image sheaf morphism sends each pair to its direct-image pair. -/
theorem finitePartOpenMap_pair {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') {T : Over S} (p : FinitePart.Point f' T) :
    (finitePartOpenMap j hcomm).hom.app (op T) p = FinitePart.Point.map j hcomm p := rfl

/-- Direct image along an open immersion is injective on finite-part sections over every test scheme. -/
theorem finitePartOpenMap_injective {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') (T : (Over S)ᵒᵖ) :
    Function.Injective fun (p : FinitePart.Point f' T.unop) ↦
      FinitePart.Point.map j hcomm p := sorry

/-- The direct-image morphism of finite-part sheaves induced by an open immersion is a monomorphism. -/
instance instMono_finitePartOpenMap {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') : Mono (finitePartOpenMap j hcomm) :=
  Sheaf.mono_of_injective (finitePartOpenMap j hcomm) (finitePartOpenMap_injective j hcomm)

end AlgebraicGeometry.AlgebraicSpace
