module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.PNat.Basic
public import stacks_project.Chap30.Lemma_30_28_1_AdicThickening
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdicThickening

/-!
# Adic thickenings of an algebraic space over an affine base

The canonical adic objects, maps, and their specifications are available from
the shared mathematical owner.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AdicThickening

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.spec :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      AlgebraicSpace (Spec (CommRingCat.of A)))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.spec_def :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      spec I n = ofOver (Over.mk (Scheme.AdicThickening.toAmbient I n)))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.toAmbient :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      spec I n ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.toAmbient_def :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      toAmbient I n =
      ofOverHomMk (Scheme.AdicThickening.toAmbient I n)
        (Category.comp_id (Scheme.AdicThickening.toAmbient I n)))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.specTransition :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      spec I n ⟶ spec I (n + 1))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.specTransition_def :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      specTransition I n =
      ofOverHomMk (Scheme.AdicThickening.specTransition I n)
        (Scheme.AdicThickening.specTransition_comp_toAmbient I n))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.specTransition_comp_toAmbient :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      specTransition I n ≫ toAmbient I (n + 1) = toAmbient I n)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.toAmbient_succ_factor :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      toAmbient I n ≫ 𝟙 (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) =
      specTransition I n ≫ toAmbient I (n + 1))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stage :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ+),
      AlgebraicSpace (Spec (CommRingCat.of A)))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stage_def :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+),
      stage X I n = pullback (toBase X) (toAmbient I n))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.ι :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ+),
      stage X I n ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.ι_eq_fst :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+),
      ι X I n = pullback.fst (toBase X) (toAmbient I n))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.toSpec :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ+),
      stage X I n ⟶ spec I n)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.toSpec_eq_snd :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+),
      toSpec X I n = pullback.snd (toBase X) (toAmbient I n))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.isPullback_ι_toSpec :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (I : Ideal A) (n : ℕ+),
      IsPullback (ι X I n) (toSpec X I n) (toBase X) (toAmbient I n))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.transition :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+),
      stage X I n ⟶ stage X I (n + 1))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.transition_ι :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+),
      transition X I n ≫ ι X I (n + 1) = ι X I n)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.transition_toSpec :
    ∀ {A : Type u} [CommRing A] (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (I : Ideal A) (n : ℕ+),
      transition X I n ≫ toSpec X I (n + 1) = toSpec X I n ≫ specTransition I n)

end AlgebraicGeometry.AlgebraicSpace.AdicThickening
