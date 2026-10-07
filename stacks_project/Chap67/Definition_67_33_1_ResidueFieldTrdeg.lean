module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.ResidueFieldTrdeg
public import stacks_project.Chap67.Lemma_67_22_5
public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal

/-!
# Residue-field transcendence degree of morphisms of algebraic spaces at a point

The transcendence degree of a source point over its image is the étale-local
germ property of Descent Lemma 35.33.7, tested on étale scheme squares as in
Lemma 67.22.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped ENat

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- The transcendence degree of `x / f(x)` is `r` if some étale scheme square
through `x` has residue-field transcendence degree `r` on the induced germ
morphism. -/
def ResidueFieldTrdegEqAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (r : ℕ∞) (x : Points X) : Prop :=
  existsEtaleSquareAt (residueFieldTrdegEq r) f x

/-- Residue-field transcendence degree `r` at `x` is the existence of an étale
scheme square through `x` whose induced germ morphism has residue-field
transcendence degree `r`. -/
theorem residueFieldTrdegEqAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (r : ℕ∞) (x : Points X) :
    ResidueFieldTrdegEqAt f r x ↔ existsEtaleSquareAt (residueFieldTrdegEq r) f x :=
  sorry

/-- Residue-field transcendence degree `r` at `x` holds if and only if every
étale scheme square through `x` has residue-field transcendence degree `r` on
the induced germ morphism. -/
theorem residueFieldTrdegEqAt_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (r : ℕ∞) (x : Points X) :
    ResidueFieldTrdegEqAt f r x ↔ forallEtaleSquareAt (residueFieldTrdegEq r) f x :=
  sorry

namespace ResidueFieldTrdegEqAt

/-- An étale scheme square over `f` through `x` whose induced germ morphism has
residue-field transcendence degree `r` witnesses `ResidueFieldTrdegEqAt f r x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {r : ℕ∞}
    {x : Points X} {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x)
    (hr : residueFieldTrdegEq r (ofOverGermHom h u)) :
    ResidueFieldTrdegEqAt f r x :=
  sorry

/-- If the residue-field transcendence degree of `x / f(x)` is `r`, then the
induced germ morphism of any étale scheme square through `x` has residue-field
transcendence degree `r`. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {r : ℕ∞}
    {x : Points X} (hf : ResidueFieldTrdegEqAt f r x) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    residueFieldTrdegEq r (ofOverGermHom h u) :=
  sorry

end ResidueFieldTrdegEqAt

/-- Given one étale scheme square over `f` through `x`, the residue-field
transcendence degree of `x / f(x)` is `r` if and only if the induced germ
morphism has residue-field transcendence degree `r`. -/
theorem residueFieldTrdegEqAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {r : ℕ∞} {x : Points X}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    ResidueFieldTrdegEqAt f r x ↔ residueFieldTrdegEq r (ofOverGermHom h u) :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the residue-field transcendence degree at the image of `u` is `r` if and only
if the induced germ morphism has residue-field transcendence degree `r`. -/
theorem residueFieldTrdegEqAt_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (r : ℕ∞) (u : U.left) :
    ResidueFieldTrdegEqAt (ofOverMap h) r (ofOver.pointsEquiv U u) ↔
      residueFieldTrdegEq r (ofOverGermHom h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
