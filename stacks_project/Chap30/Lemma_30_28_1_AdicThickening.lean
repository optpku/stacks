module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Adic thickenings of a morphism to an affine base

For an ideal `I` of a ring `A` and a morphism `f : X ⟶ Spec(A)`, the adic
stage `S_n` is `Spec(A ⧸ I^n)` and the adic stage `X_n` is the chosen fibre
product `X ×_S S_n`. Successor maps are induced by `Ideal.Quotient.factorPowSucc`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AdicThickening

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The spectrum `S_n = Spec(A ⧸ I^n)` of an adic stage. -/
def spec (I : Ideal A) (n : ℕ+) : Scheme.{u} :=
  Spec (CommRingCat.of (A ⧸ I ^ (n : ℕ)))

/-- The adic stage spectrum is `Spec` of the corresponding ideal-power quotient. -/
theorem spec_def (I : Ideal A) (n : ℕ+) :
    spec I n = Spec (CommRingCat.of (A ⧸ I ^ (n : ℕ))) :=
  sorry

/-- The canonical morphism `S_n ⟶ S` induced by `A ⟶ A ⧸ I^n`. -/
def toAmbient (I : Ideal A) (n : ℕ+) : spec I n ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n : ℕ))))

/-- `toAmbient` is `Spec.map` of the quotient map `A ⟶ A ⧸ I^n`. -/
theorem toAmbient_def (I : Ideal A) (n : ℕ+) :
    toAmbient I n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n : ℕ)))) :=
  sorry

/-- The closed immersion `i_n : S_n ⟶ S_{n+1}` induced by `A ⧸ I^{n+1} ⟶ A ⧸ I^n`. -/
def specTransition (I : Ideal A) (n : ℕ+) : spec I n ⟶ spec I (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n : ℕ)))

/-- `specTransition` is `Spec.map` of `Ideal.Quotient.factorPowSucc`. -/
theorem specTransition_def (I : Ideal A) (n : ℕ+) :
    specTransition I n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n : ℕ))) :=
  sorry

/-- Successive morphisms to `Spec(A)` factor through `specTransition`. -/
theorem specTransition_comp_toAmbient (I : Ideal A) (n : ℕ+) :
    specTransition I n ≫ toAmbient I (n + 1) = toAmbient I n :=
  sorry

/-- The identity-extended form of `specTransition_comp_toAmbient` used by `pullback.map`. -/
theorem toAmbient_succ_factor (I : Ideal A) (n : ℕ+) :
    toAmbient I n ≫ 𝟙 (Spec (CommRingCat.of A)) =
      specTransition I n ≫ toAmbient I (n + 1) :=
  sorry

/-- The adic stage `X_n = X ×_S S_n`. -/
def stage (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) : Scheme.{u} :=
  pullback f (toAmbient I n)

/-- The adic stage is the chosen fibre product along `toAmbient`. -/
theorem stage_def (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    stage f I n = pullback f (toAmbient I n) :=
  sorry

/-- The closed immersion `X_n ⟶ X` of an adic stage. -/
def ι (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) : stage f I n ⟶ X :=
  pullback.fst f (toAmbient I n)

/-- The stage inclusion is the first projection of the fibre product. -/
theorem ι_eq_fst (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    ι f I n = pullback.fst f (toAmbient I n) :=
  sorry

/-- The structure morphism `X_n ⟶ S_n` of an adic stage. -/
def toSpec (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    stage f I n ⟶ spec I n :=
  pullback.snd f (toAmbient I n)

/-- The stage structure morphism is the second projection of the fibre product. -/
theorem toSpec_eq_snd (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    toSpec f I n = pullback.snd f (toAmbient I n) :=
  sorry

/-- The displayed square of an adic stage is a pullback square. -/
theorem isPullback_ι_toSpec (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    IsPullback (ι f I n) (toSpec f I n) f (toAmbient I n) :=
  sorry

/-- The closed immersion `i_n : X_n ⟶ X_{n+1}` of successive adic stages. -/
def transition (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    stage f I n ⟶ stage f I (n + 1) :=
  pullback.map f (toAmbient I n) f (toAmbient I (n + 1)) (𝟙 X)
    (specTransition I n) (𝟙 (Spec (CommRingCat.of A)))
    (Category.id_comp f).symm (toAmbient_succ_factor I n)

/-- Stage transitions lie over `X` through `ι`. -/
theorem transition_ι (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    transition f I n ≫ ι f I (n + 1) = ι f I n :=
  sorry

/-- Stage transitions lie over the adic spectra through `toSpec`. -/
theorem transition_toSpec (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    transition f I n ≫ toSpec f I (n + 1) = toSpec f I n ≫ specTransition I n :=
  sorry

end AlgebraicGeometry.Scheme.AdicThickening
