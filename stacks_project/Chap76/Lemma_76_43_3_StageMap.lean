/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_43_1_AdicThickening

/-!
# Base change of morphisms of algebraic spaces to adic stages

A morphism of algebraic spaces over `Spec(A)` induces maps between the chosen
fibre products `X ×_S S_n` and `Y ×_S S_n` by `pullback.map`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AdicThickening

variable {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The base change of a morphism `G : X ⟶ Y` of algebraic spaces over `Spec(A)`
to the adic stage `S_n`. -/
def stageMap {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A) (G : X ⟶ Y)
    (n : ℕ+) : stage X I n ⟶ stage Y I n :=
  pullback.map (toBase X) (toAmbient I n) (toBase Y) (toAmbient I n) G
    (𝟙 (spec I n)) (𝟙 (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))))
    ((Category.comp_id (toBase X)).trans (eq_toBase (G ≫ toBase Y)).symm)
    ((Category.comp_id (toAmbient I n)).trans (Category.id_comp (toAmbient I n)).symm)

/-- The induced stage map lies over `G` through the stage inclusions `ι`. -/
theorem stageMap_ι {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) (n : ℕ+) :
    stageMap I G n ≫ ι Y I n = ι X I n ≫ G :=
  sorry

/-- The induced stage map lies over `S_n` through `toSpec`. -/
theorem stageMap_toSpec {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) (n : ℕ+) :
    stageMap I G n ≫ toSpec Y I n = toSpec X I n :=
  sorry

/-- The induced stage maps are compatible with successor transitions. -/
theorem stageMap_transition {Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    (I : Ideal A) (G : X ⟶ Y) (n : ℕ+) :
    stageMap I G n ≫ transition Y I n = transition X I n ≫ stageMap I G (n + 1) :=
  sorry

/-- The identity of an algebraic space over `Spec(A)` induces the identity on each
adic stage. -/
theorem stageMap_id (I : Ideal A) (n : ℕ+) :
    stageMap I (𝟙 X) n = 𝟙 (stage X I n) :=
  sorry

/-- Base change to an adic stage preserves composition of morphisms of algebraic
spaces over `Spec(A)`. -/
theorem stageMap_comp {Y Z : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) (H : Y ⟶ Z) (n : ℕ+) :
    stageMap I (G ≫ H) n = stageMap I G n ≫ stageMap I H n :=
  sorry

/-- A morphism of adic stages is the base change of `G` iff it lies over `G` through `ι`
and over `S_n` through `toSpec`. -/
theorem eq_stageMap_iff {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) {n : ℕ+} (g : stage X I n ⟶ stage Y I n) :
    g = stageMap I G n ↔
      g ≫ ι Y I n = ι X I n ≫ G ∧ g ≫ toSpec Y I n = toSpec X I n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AdicThickening
