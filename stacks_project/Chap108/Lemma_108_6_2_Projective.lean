/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap69.Lemma_69_20_1_ProjectiveSpace
public import stacks_project.Chap69.Lemma_69_20_1_Twist
public import stacks_project.Chap108.Lemma_108_5_10_Hilbert

/-!
# Hilbert Quot of finitely presented sheaves on projective space over a base

The source specialization of `quotHilbert` to a quasi-coherent sheaf on
`P^n_B`, with `𝒪(1)` as the twisting sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The structure morphism `P^n_B ⟶ B` is of finite presentation. -/
instance instFinitePresentation_projectiveToBase (n : ℕ) {S : Scheme.{u}}
    (B : AlgebraicSpace S) :
    FinitePresentation (ProjectiveSpace.toBase n B) :=
  sorry

/-- The structure morphism `P^n_B ⟶ B` is separated. -/
instance instSeparated_projectiveToBase (n : ℕ) {S : Scheme.{u}}
    (B : AlgebraicSpace S) :
    Separated (ProjectiveSpace.toBase n B) :=
  sorry

/-- The Hilbert Quot functor of quotients of a quasi-coherent sheaf on `P^n_B`
with Hilbert polynomial `P` with respect to `𝒪(1)`. -/
abbrev quotHilbert_projectiveOver (n : ℕ) {S : Scheme.{u}}
    (B : AlgebraicSpace S) (F : (ProjectiveSpace n B).Modules)
    [F.IsQuasicoherent] (P : ℤ → ℤ) :=
  quotHilbert (ProjectiveSpace.toBase n B) F
    (ProjectiveSpace.twistingSheaf n B) P

/-- `quotHilbert_projectiveOver` is `quotHilbert` of the structure morphism of
`P^n_B`, the given quasi-coherent sheaf, and `𝒪(1)`. -/
theorem quotHilbert_projectiveOver_eq (n : ℕ) {S : Scheme.{u}}
    (B : AlgebraicSpace S) (F : (ProjectiveSpace n B).Modules)
    [F.IsQuasicoherent] (P : ℤ → ℤ) :
    quotHilbert_projectiveOver n B F P =
      quotHilbert (ProjectiveSpace.toBase n B) F
        (ProjectiveSpace.twistingSheaf n B) P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
