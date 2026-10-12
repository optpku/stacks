/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap101.Lemma_101_4_10
public import stacks_project.Chap101.Lemma_101_7_4
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage

/-!
# Relative quasi-coherent Leray spectral sequence for algebraic stacks

A pair of quasi-compact quasi-separated 1-morphisms of algebraic stacks
yields a Leray spectral sequence in `QCoh` whose `E₂`-page is quasi-coherent
higher direct images of quasi-coherent higher direct images, abutting to
quasi-coherent higher direct images of the composite.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The displayed `E₂^{p, q}` object `R^p g_{QCoh,*}(R^q f_{QCoh,*} F)` of the
relative quasi-coherent Leray spectral sequence. -/
noncomputable abbrev qcohRelativeLerayPageTwo {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (F : QCoh X) (p q : ℕ) : QCoh Z :=
  QCoh.higherDirectImage g (QCoh.higherDirectImage f F q) p

/-- `qcohRelativeLerayPageTwo f g F p q` is `R^p g_{QCoh,*}` of
`R^q f_{QCoh,*} F`. -/
theorem qcohRelativeLerayPageTwo_eq {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (F : QCoh X) (p q : ℕ) :
    qcohRelativeLerayPageTwo f g F p q =
      QCoh.higherDirectImage g (QCoh.higherDirectImage f F q) p :=
  rfl

/-- Lemma 103.11.5: Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be quasi-compact and
quasi-separated morphisms of algebraic stacks, and let `F` be a quasi-coherent
sheaf on `𝒳`. Then there exists a spectral sequence with
`E₂^{p, q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} F)` converging to
`R^{p+q}(g ∘ f)_{QCoh,*} F`. The displayed page is
`qcohRelativeLerayPageTwo f g F p q` and the abutment is
`QCoh.higherDirectImage (f ≫ g) F`. -/
@[stacks 0783]
theorem exists_qcohRelativeLeraySpectralSequence {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : QCoh X)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    ∃ (E : CohomologicalSpectralSequenceNat (QCoh Z) 2)
      (pageTwoIso : ∀ p q : ℕ,
        (E.page 2 le_rfl).X (p, q) ≅ qcohRelativeLerayPageTwo f g F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ QCoh.higherDirectImage (f ≫ g) F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
