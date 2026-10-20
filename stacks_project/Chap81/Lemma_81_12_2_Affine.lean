module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.Affine

/-!
# Affine glueable algebraic spaces for a Beauville–Laszlo pair

This source-facing module records the public types of the affine restriction of
the canonical Beauville–Laszlo functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

#check (affineGlueableProperty :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → ObjectProperty (Over (space R)))

#check (affineGlueableProperty_iff :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → (Y : Over (space R)) →
      (affineGlueableProperty R' f Y ↔
        AlgebraicSpace.IsAffine Y.left ∧ glueableProperty R' f Y))

#check (affineTripleProperty :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → ObjectProperty (category R' f))

#check (affineTripleProperty_iff :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → (obj : category R' f) →
      (affineTripleProperty R' f obj ↔
        AlgebraicSpace.IsAffine obj.fst.left ∧
          AlgebraicSpace.IsAffine (overlap obj).left ∧
          AlgebraicSpace.IsAffine obj.snd.left))

#check (functor_obj_mem_affineTriple :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → {Y : Over (space R)} → (hY : AlgebraicSpace.IsAffine Y.left) →
      affineTripleProperty R' f ((functor R' f).obj Y))

#check (affineGlueableFunctor :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → (affineGlueableProperty R' f).FullSubcategory ⥤
      (affineTripleProperty R' f).FullSubcategory)

#check (affineGlueableFunctor_comp_ι :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) →
      affineGlueableFunctor R' f ⋙ (affineTripleProperty R' f).ι =
        (affineGlueableProperty R' f).ι ⋙ functor R' f)

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
