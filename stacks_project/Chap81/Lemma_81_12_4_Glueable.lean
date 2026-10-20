module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.GlueableFunctor

/-!
# Glueable algebraic spaces for a Beauville–Laszlo pair

This source-facing module records the public types of the reusable glueable
algebraic-space API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/- The object property of glueable algebraic spaces over `Spec R`. -/
#check (glueableProperty :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → ObjectProperty (Over (space R)))

/- Its defining affine étale test condition. -/
#check (glueableProperty_iff :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → (Y : Over (space R)) →
      (glueableProperty R' f Y ↔
        ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
          (φ : ofOver T ⟶ Y.left) [Etale φ],
          Scheme.Hom.glueableGlobalSections R' f T))

/- The canonical affine-cover characterization, owned by the algebraic-space API. -/
#check (AlgebraicGeometry.AlgebraicSpace.exists_affineEtale_glueableGlobalSections_iff :
  {R R' : Type u} → [CommRing R] → [CommRing R'] → [Algebra R R'] → (f : R) →
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] →
    (Y : AlgebraicSpace (Spec (CommRingCat.of R))) →
      ((∃ (I : Type u) (hsmall : Small.{u} I)
          (U : I → Over (Spec (CommRingCat.of R)))
          (φ : ∀ i, ofOver (U i) ⟶ Y),
        (∀ i, AlgebraicGeometry.IsAffine (U i).left) ∧
          EtaleCovering (fun i ↦ Over.mk (φ i)) ∧
          ∀ i, Scheme.Hom.glueableGlobalSections R' f (U i)) ↔
        ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
          (φ : ofOver T ⟶ Y) [Etale φ],
          Scheme.Hom.glueableGlobalSections R' f T))

/- The restriction of the canonical Beauville–Laszlo functor. -/
#check (glueableFunctor :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) → (glueableProperty R' f).FullSubcategory ⥤ category R' f)

/- Its defining composition equation. -/
#check (glueableFunctor_eq :
  {R : Type u} → (R' : Type u) → [CommRing R] → [CommRing R'] → [Algebra R R'] →
    (f : R) →
      glueableFunctor R' f = (glueableProperty R' f).ι ⋙ functor R' f)

/- Faithfulness of the restricted functor for a glueing pair. -/
#check (glueableFunctor_faithful :
  {R R' : Type u} → [CommRing R] → [CommRing R'] → [Algebra R R'] → (f : R) →
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] →
    (glueableFunctor R' f).Faithful)

/- Injectivity on morphisms of glueable algebraic spaces. -/
#check (functor_map_injective :
  {R R' : Type u} → [CommRing R] → [CommRing R'] → [Algebra R R'] → (f : R) →
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] →
    {Y Z : Over (space R)} → (hY : glueableProperty R' f Y) →
      (hZ : glueableProperty R' f Z) →
      Function.Injective (fun α : Y ⟶ Z ↦ (functor R' f).map α))

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
