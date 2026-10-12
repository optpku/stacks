/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap81.«81_12_0_1_Glueing»
public import stacks_project.Chap81.Lemma_81_12_1
public import stacks_project.Chap81.Lemma_81_12_1_Glueable

/-!
# Glueable algebraic spaces for a Beauville–Laszlo pair

An algebraic space `Y` over `X = Spec R` is glueable for `(algebraMap R R', f)`
when every étale affine test morphism into `Y` has glueable global sections.
Restricting `functor R' f` along the corresponding object property yields the
canonical functor on that full subcategory.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- The object property of algebraic spaces `Y` over `X = space R` that are
glueable for `(algebraMap R R', f)`: every étale `φ : ofOver T ⟶ Y.left` with
`T.left` affine has glueable global sections. -/
abbrev glueableProperty {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) : ObjectProperty (Over (space R)) :=
  fun Y ↦
    ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
      (φ : ofOver T ⟶ Y.left) [Etale φ],
      Scheme.Hom.glueableGlobalSections R' f T

/-- Membership in `glueableProperty R' f` is glueability of global sections on
every étale affine test morphism into `Y.left`. -/
theorem glueableProperty_iff {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) (Y : Over (space R)) :
    glueableProperty R' f Y ↔
      ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
        (φ : ofOver T ⟶ Y.left) [Etale φ],
        Scheme.Hom.glueableGlobalSections R' f T :=
  sorry

/-- For a glueing pair, `glueableProperty R' f Y` is equivalent to the existence of
an étale covering of `Y.left` by affine `ofOver (U i)` with glueable global
sections, with index type `Small.{u}`. -/
theorem glueableProperty_iff_exists_affineEtale {R : Type u} (R' : Type u)
    [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] (Y : Over (space R)) :
    glueableProperty R' f Y ↔
      ∃ (I : Type u) (_ : Small.{u} I) (U : I → Over (Spec (CommRingCat.of R)))
        (φ : ∀ i, ofOver (U i) ⟶ Y.left),
        (∀ i, AlgebraicGeometry.IsAffine (U i).left) ∧
          EtaleCovering (fun i ↦ Over.mk (φ i)) ∧
          ∀ i, Scheme.Hom.glueableGlobalSections R' f (U i) :=
  sorry

/-- The canonical functor `Over (space R) ⥤ category R' f` restricted to the full
subcategory of glueable algebraic spaces over `X`. -/
abbrev glueableFunctor {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    (f : R) : (glueableProperty R' f).FullSubcategory ⥤ category R' f :=
  (glueableProperty R' f).ι ⋙ functor R' f

/-- `glueableFunctor R' f` is the composite of `ι` with `functor R' f`. -/
theorem glueableFunctor_eq {R : Type u} (R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) :
    glueableFunctor R' f = (glueableProperty R' f).ι ⋙ functor R' f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
