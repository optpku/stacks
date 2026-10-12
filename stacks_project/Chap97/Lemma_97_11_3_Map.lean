/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.Lemma_97_11_1_Sheaf

/-!
# Functoriality of restriction of scalars in the source

A morphism `h : X' ⟶ X` of algebraic spaces induces a morphism
`restrictionOfScalars (h ≫ f) g ⟶ restrictionOfScalars f g` by postcomposition
on lifts, together with the associated sheaf and groupoid-fibration maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

namespace Pair

/-- Postcomposition of a restriction-of-scalars pair along `h : X' ⟶ X`, sending
`(a, b)` to `(a, b ≫ h)`. -/
def postcomp {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair (h ≫ f) g T) : Pair f g T where
  base := p.base
  lift := p.lift ≫ h
  overZ := sorry

/-- The base morphism of `postcomp h f g p` is `p.base`. -/
theorem postcomp_base {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair (h ≫ f) g T) :
    (postcomp h f g p).base = p.base :=
  sorry

/-- The lift of `postcomp h f g p` is `p.lift ≫ h`. -/
theorem postcomp_lift {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair (h ≫ f) g T) :
    (postcomp h f g p).lift = p.lift ≫ h :=
  sorry

/-- The postcomposed lift remains a morphism over `Z`. -/
theorem postcomp_overZ {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair (h ≫ f) g T) :
    (postcomp h f g p).lift ≫ f = fiberSnd g (postcomp h f g p).base :=
  sorry

end Pair

/-- The presheaf morphism `restrictionOfScalars (h ≫ f) g ⟶ restrictionOfScalars f g`
induced by `h : X' ⟶ X`. -/
def map {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X) (f : X ⟶ Z)
    (g : Z ⟶ B) : restrictionOfScalars (h ≫ f) g ⟶ restrictionOfScalars f g where
  app T := TypeCat.ofHom fun p ↦ Pair.postcomp h f g p
  naturality := sorry

/-- Components of `map h f g` are `Pair.postcomp h f g`. -/
theorem map_app {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) (p : Pair (h ≫ f) g T.unop) :
    (map h f g).app T p = Pair.postcomp h f g p :=
  sorry

/-- The sheaf morphism `restrictionOfScalarsSheaf (h ≫ f) g ⟶ restrictionOfScalarsSheaf f g`
induced by `h : X' ⟶ X`. -/
def mapSheaf {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) :
    restrictionOfScalarsSheaf (h ≫ f) g ⟶ restrictionOfScalarsSheaf f g :=
  Sheaf.homEquiv.symm (map h f g)

/-- The underlying presheaf morphism of `mapSheaf` is `map`. -/
theorem mapSheaf_hom {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) : (mapSheaf h f g).hom = map h f g :=
  sorry

/-- The category fibred in groupoids associated to `restrictionOfScalars f g`,
obtained by the discrete Grothendieck construction and forgetting from sets to
groupoids. -/
def toGroupoids {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) : GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj
    ((Sets.ofPresheaf (Over S)).obj (restrictionOfScalars f g))

/-- `toGroupoids f g` is the discrete Grothendieck construction of
`restrictionOfScalars f g`, forgotten from sets to groupoids. -/
theorem toGroupoids_spec {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) :
    toGroupoids f g =
      (Sets.toGroupoids (Over S)).obj
        ((Sets.ofPresheaf (Over S)).obj (restrictionOfScalars f g)) :=
  sorry

/-- The 1-morphism `toGroupoids (h ≫ f) g ⟶ toGroupoids f g` of categories fibred
in groupoids induced by `h : X' ⟶ X`. -/
def mapGroupoids {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S} (h : X' ⟶ X)
    (f : X ⟶ Z) (g : Z ⟶ B) : toGroupoids (h ≫ f) g ⟶ toGroupoids f g :=
  (Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map (map h f g))

/-- `mapGroupoids h f g` is `Sets.toGroupoids` applied to the discrete Grothendieck
construction of `map h f g`. -/
theorem mapGroupoids_spec {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B) :
    mapGroupoids h f g =
      (Sets.toGroupoids (Over S)).map
        ((Sets.ofPresheaf (Over S)).map (map h f g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
