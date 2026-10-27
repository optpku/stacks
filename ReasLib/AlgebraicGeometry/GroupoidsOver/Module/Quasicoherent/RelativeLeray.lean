/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Composition
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment

/-!
# Relative quasi-coherent Leray spectral sequence for algebraic stacks

A pair of quasi-compact quasi-separated morphisms of algebraic stacks yields
a spectral sequence of quasi-coherent modules whose second page consists of
iterated higher direct images and which converges to the higher direct images
of the composite.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The second-page object `R^p g_{QCoh,*}(R^q f_{QCoh,*} F)` of the relative
quasi-coherent Leray spectral sequence. -/
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

/-- Composable quasi-compact quasi-separated morphisms of algebraic stacks
admit a spectral sequence of quasi-coherent modules with second page
`R^p g_{QCoh,*}(R^q f_{QCoh,*} F)`, converging to
`R^{p+q}(g ∘ f)_{QCoh,*} F`. -/
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
