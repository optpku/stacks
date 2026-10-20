module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.FiberStalkDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt

/-!
# Fibre-stalk dimension of morphisms of algebraic spaces at a point

The dimension of the local ring of the fibre at a source point is tested on
étale scheme squares through that point, using the induced morphism of germs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- The dimension of the local ring of the fibre of `f : X ⟶ Y` at a point `x`
of `|X|` is `d` if some étale scheme square through `x` has fibre-stalk Krull
dimension `d` on the induced germ morphism. -/
def FiberStalkDimEqAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) : Prop :=
  existsEtaleSquareAt (fiberStalkKrullDimEq d) f x

/-- Fibre-stalk dimension `d` at `x` is the existence of an étale scheme square
through `x` whose induced germ morphism has fibre-stalk Krull dimension `d`. -/
theorem fiberStalkDimEqAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) :
    FiberStalkDimEqAt f d x ↔ existsEtaleSquareAt (fiberStalkKrullDimEq d) f x :=
  sorry

/-- Fibre-stalk dimension `d` at `x` holds if and only if every étale scheme
square through `x` has fibre-stalk Krull dimension `d` on the induced germ
morphism. -/
theorem fiberStalkDimEqAt_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) :
    FiberStalkDimEqAt f d x ↔ forallEtaleSquareAt (fiberStalkKrullDimEq d) f x :=
  sorry

namespace FiberStalkDimEqAt

/-- An étale scheme square over `f` through `x` whose induced germ morphism has
fibre-stalk Krull dimension `d` witnesses `FiberStalkDimEqAt f d x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞}
    {x : Points X} {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x)
    (hd : fiberStalkKrullDimEq d (ofOverGermHom h u)) :
    FiberStalkDimEqAt f d x :=
  sorry

/-- If the fibre-stalk dimension of `f` at `x` is `d`, then the induced germ
morphism of any étale scheme square through `x` has fibre-stalk Krull
dimension `d`. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞}
    {x : Points X} (hf : FiberStalkDimEqAt f d x) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    fiberStalkKrullDimEq d (ofOverGermHom h u) :=
  sorry

end FiberStalkDimEqAt

/-- Given one étale scheme square over `f` through `x`, the fibre-stalk
dimension of `f` at `x` is `d` if and only if the induced germ morphism has
fibre-stalk Krull dimension `d`. -/
theorem fiberStalkDimEqAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞} {x : Points X}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    FiberStalkDimEqAt f d x ↔ fiberStalkKrullDimEq d (ofOverGermHom h u) :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the fibre-stalk dimension at the image of `u` is `d` if and only if the
induced germ morphism has fibre-stalk Krull dimension `d`. -/
theorem fiberStalkDimEqAt_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (d : ℕ∞) (u : U.left) :
    FiberStalkDimEqAt (ofOverMap h) d (ofOver.pointsEquiv U u) ↔
      fiberStalkKrullDimEq d (ofOverGermHom h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
