/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.PNat.Basic
public import stacks_project.Chap30.Lemma_30_28_1_AdicThickening
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Adic thickenings of an algebraic space over an affine base

For an ideal `I` of a ring `A` and an algebraic space `X` over `Spec(A)`,
the adic stage `S_n` is `Spec(A ⧸ I^n)` as an algebraic space over `Spec(A)`,
and the adic stage `X_n` is the chosen fibre product `X ×_S S_n`. Successor
maps are induced by `Scheme.AdicThickening.specTransition`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AdicThickening

variable {A : Type u} [CommRing A]

/-- The spectrum `S_n = Spec(A ⧸ I^n)` of an adic stage, as an algebraic space
over `Spec(A)`. -/
def spec (I : Ideal A) (n : ℕ+) : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (Scheme.AdicThickening.toAmbient I n))

/-- The adic stage spectrum is the algebraic space associated to the scheme
morphism `Scheme.AdicThickening.toAmbient I n`. -/
theorem spec_def (I : Ideal A) (n : ℕ+) :
    spec I n = ofOver (Over.mk (Scheme.AdicThickening.toAmbient I n)) :=
  sorry

/-- The canonical morphism `S_n ⟶ S` of algebraic spaces over `Spec(A)`. -/
def toAmbient (I : Ideal A) (n : ℕ+) :
    spec I n ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ofOverHomMk (Scheme.AdicThickening.toAmbient I n)
    (Category.comp_id (Scheme.AdicThickening.toAmbient I n))

/-- `toAmbient` is `ofOverHomMk` of `Scheme.AdicThickening.toAmbient`. -/
theorem toAmbient_def (I : Ideal A) (n : ℕ+) :
    toAmbient I n =
      ofOverHomMk (Scheme.AdicThickening.toAmbient I n)
        (Category.comp_id (Scheme.AdicThickening.toAmbient I n)) :=
  sorry

/-- The closed immersion `S_n ⟶ S_{n+1}` induced by `A ⧸ I^{n+1} ⟶ A ⧸ I^n`. -/
def specTransition (I : Ideal A) (n : ℕ+) : spec I n ⟶ spec I (n + 1) :=
  ofOverHomMk (Scheme.AdicThickening.specTransition I n)
    (Scheme.AdicThickening.specTransition_comp_toAmbient I n)

/-- `specTransition` is `ofOverHomMk` of `Scheme.AdicThickening.specTransition`. -/
theorem specTransition_def (I : Ideal A) (n : ℕ+) :
    specTransition I n =
      ofOverHomMk (Scheme.AdicThickening.specTransition I n)
        (Scheme.AdicThickening.specTransition_comp_toAmbient I n) :=
  sorry

/-- Successive morphisms to `Spec(A)` factor through `specTransition`. -/
theorem specTransition_comp_toAmbient (I : Ideal A) (n : ℕ+) :
    specTransition I n ≫ toAmbient I (n + 1) = toAmbient I n :=
  sorry

/-- The identity-extended form of `specTransition_comp_toAmbient` used by
`pullback.map`. -/
theorem toAmbient_succ_factor (I : Ideal A) (n : ℕ+) :
    toAmbient I n ≫ 𝟙 (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) =
      specTransition I n ≫ toAmbient I (n + 1) :=
  sorry

/-- The adic stage `X_n = X ×_S S_n`. -/
def stage (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ+) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  pullback (toBase X) (toAmbient I n)

/-- The adic stage is the chosen fibre product of `toBase X` along `toAmbient`. -/
theorem stage_def (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+) : stage X I n = pullback (toBase X) (toAmbient I n) :=
  sorry

/-- The closed immersion `X_n ⟶ X` of an adic stage. -/
def ι (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ+) :
    stage X I n ⟶ X :=
  pullback.fst (toBase X) (toAmbient I n)

/-- The stage inclusion is the first projection of the fibre product. -/
theorem ι_eq_fst (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+) : ι X I n = pullback.fst (toBase X) (toAmbient I n) :=
  sorry

/-- The structure morphism `X_n ⟶ S_n` of an adic stage. -/
def toSpec (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) (n : ℕ+) :
    stage X I n ⟶ spec I n :=
  pullback.snd (toBase X) (toAmbient I n)

/-- The stage structure morphism is the second projection of the fibre product. -/
theorem toSpec_eq_snd (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+) : toSpec X I n = pullback.snd (toBase X) (toAmbient I n) :=
  sorry

/-- The displayed square of an adic stage is a pullback square. -/
theorem isPullback_ι_toSpec (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (I : Ideal A) (n : ℕ+) :
    IsPullback (ι X I n) (toSpec X I n) (toBase X) (toAmbient I n) :=
  sorry

/-- The closed immersion `i_n : X_n ⟶ X_{n+1}` of successive adic stages. -/
def transition (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+) : stage X I n ⟶ stage X I (n + 1) :=
  pullback.map (toBase X) (toAmbient I n) (toBase X) (toAmbient I (n + 1)) (𝟙 X)
    (specTransition I n) (𝟙 (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))))
    (Category.id_comp (toBase X)).symm (toAmbient_succ_factor I n)

/-- Stage transitions lie over `X` through `ι`. -/
theorem transition_ι (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A)
    (n : ℕ+) : transition X I n ≫ ι X I (n + 1) = ι X I n :=
  sorry

/-- Stage transitions lie over the adic spectra through `toSpec`. -/
theorem transition_toSpec (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (I : Ideal A) (n : ℕ+) :
    transition X I n ≫ toSpec X I (n + 1) = toSpec X I n ≫ specTransition I n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AdicThickening
