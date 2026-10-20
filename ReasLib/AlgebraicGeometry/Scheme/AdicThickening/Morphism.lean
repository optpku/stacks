module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.AdicThickening

/-!
# Base change of morphisms to adic stages

A morphism over `Spec(A)` induces maps between the chosen fibre products
`X ×_S S_n` and `Y ×_S S_n` by `pullback.map`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AdicThickening

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The base change of a morphism `G : X ⟶ Y` over `Spec(A)` to the adic stage `S_n`. -/
def stageMap {Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (G : X ⟶ Y)
    (hG : G ≫ fY = fX) (n : ℕ+) : stage fX I n ⟶ stage fY I n :=
  pullback.map fX (toAmbient I n) fY (toAmbient I n) G
    (𝟙 (spec I n)) (𝟙 (Spec (CommRingCat.of A)))
    ((Category.comp_id fX).trans hG.symm)
    ((Category.comp_id (toAmbient I n)).trans (Category.id_comp (toAmbient I n)).symm)

/-- The induced stage map lies over `G` through the stage inclusions `ι`. -/
theorem stageMap_ι {Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (G : X ⟶ Y)
    (hG : G ≫ fY = fX) (n : ℕ+) :
    stageMap fX fY I G hG n ≫ ι fY I n = ι fX I n ≫ G :=
  sorry

/-- The induced stage map lies over `S_n` through `toSpec`. -/
theorem stageMap_toSpec {Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (G : X ⟶ Y)
    (hG : G ≫ fY = fX) (n : ℕ+) :
    stageMap fX fY I G hG n ≫ toSpec fY I n = toSpec fX I n :=
  sorry

/-- The induced stage maps are compatible with successor transitions. -/
theorem stageMap_transition {Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (G : X ⟶ Y)
    (hG : G ≫ fY = fX) (n : ℕ+) :
    stageMap fX fY I G hG n ≫ transition fY I n =
      transition fX I n ≫ stageMap fX fY I G hG (n + 1) :=
  sorry

/-- The identity over `Spec(A)` induces the identity on each adic stage. -/
theorem stageMap_id (fX : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ+) :
    stageMap fX fX I (𝟙 X) (Category.id_comp fX) n = 𝟙 (stage fX I n) :=
  sorry

/-- Base change to an adic stage preserves composition of morphisms over `Spec(A)`. -/
theorem stageMap_comp {Y Z : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A)) (fZ : Z ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (G : X ⟶ Y) (H : Y ⟶ Z) (hG : G ≫ fY = fX) (hH : H ≫ fZ = fY)
    (n : ℕ+) :
    stageMap fX fZ I (G ≫ H)
      ((Category.assoc G H fZ).symm.trans ((whisker_eq G hH).trans hG)) n =
      stageMap fX fY I G hG n ≫ stageMap fY fZ I H hH n :=
  sorry

/-- A morphism of adic stages is the base change of `G` iff it lies over `G` through `ι`
and over `S_n` through `toSpec`. -/
theorem eq_stageMap_iff {Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (G : X ⟶ Y)
    (hG : G ≫ fY = fX) {n : ℕ+} (g : stage fX I n ⟶ stage fY I n) :
    g = stageMap fX fY I G hG n ↔
      g ≫ ι fY I n = ι fX I n ≫ G ∧ g ≫ toSpec fY I n = toSpec fX I n :=
  sorry

end AlgebraicGeometry.Scheme.AdicThickening
