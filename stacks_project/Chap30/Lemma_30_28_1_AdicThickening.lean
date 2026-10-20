module

public import ReasLib.AlgebraicGeometry.Scheme.AdicThickening

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.AdicThickening

universe u

#check (AlgebraicGeometry.Scheme.AdicThickening.spec :
    ∀ {A : Type u} [CommRing A] (_ : Ideal A) (_ : ℕ+),
      Scheme.{u})

#check (AlgebraicGeometry.Scheme.AdicThickening.spec_def :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      spec I n = Spec (CommRingCat.of (A ⧸ I ^ (n : ℕ))))

#check (AlgebraicGeometry.Scheme.AdicThickening.toAmbient :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      spec I n ⟶ Spec (CommRingCat.of A))

#check (AlgebraicGeometry.Scheme.AdicThickening.toAmbient_def :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      toAmbient I n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n : ℕ)))))

#check (AlgebraicGeometry.Scheme.AdicThickening.specTransition :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      spec I n ⟶ spec I (n + 1))

#check (AlgebraicGeometry.Scheme.AdicThickening.specTransition_def :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      specTransition I n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n : ℕ))))

#check (AlgebraicGeometry.Scheme.AdicThickening.specTransition_comp_toAmbient :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      specTransition I n ≫ toAmbient I (n + 1) = toAmbient I n)

#check (AlgebraicGeometry.Scheme.AdicThickening.toAmbient_succ_factor :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+),
      toAmbient I n ≫ 𝟙 (Spec (CommRingCat.of A)) =
      specTransition I n ≫ toAmbient I (n + 1))

#check (AlgebraicGeometry.Scheme.AdicThickening.stage :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (_ : X ⟶ Spec (CommRingCat.of A))
      (_ : Ideal A) (_ : ℕ+),
      Scheme.{u})

#check (AlgebraicGeometry.Scheme.AdicThickening.stage_def :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      stage f I n = pullback f (toAmbient I n))

#check (AlgebraicGeometry.Scheme.AdicThickening.ι :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      stage f I n ⟶ X)

#check (AlgebraicGeometry.Scheme.AdicThickening.ι_eq_fst :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      ι f I n = pullback.fst f (toAmbient I n))

#check (AlgebraicGeometry.Scheme.AdicThickening.toSpec :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      stage f I n ⟶ spec I n)

#check (AlgebraicGeometry.Scheme.AdicThickening.toSpec_eq_snd :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      toSpec f I n = pullback.snd f (toAmbient I n))

#check (AlgebraicGeometry.Scheme.AdicThickening.isPullback_ι_toSpec :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      IsPullback (ι f I n) (toSpec f I n) f (toAmbient I n))

#check (AlgebraicGeometry.Scheme.AdicThickening.transition :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      stage f I n ⟶ stage f I (n + 1))

#check (AlgebraicGeometry.Scheme.AdicThickening.transition_ι :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      transition f I n ≫ ι f I (n + 1) = ι f I n)

#check (AlgebraicGeometry.Scheme.AdicThickening.transition_toSpec :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+),
      transition f I n ≫ toSpec f I (n + 1) = toSpec f I n ≫ specTransition I n)
