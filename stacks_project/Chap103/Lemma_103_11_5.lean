/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.RelativeLeray
import StacksCheckRecall

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

universe u

/- Lemma 103.11.5: Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be quasi-compact and
quasi-separated morphisms of algebraic stacks, and let `F` be a quasi-coherent
sheaf on `𝒳`. Then there exists a spectral sequence with
`E₂^{p, q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} F)` converging to
`R^{p+q}(g ∘ f)_{QCoh,*} F`. The displayed page is
`qcohRelativeLerayPageTwo f g F p q` and the abutment is
`QCoh.higherDirectImage (f ≫ g) F`. -/
@[stacks 0783] #check
  (AlgebraicGeometry.GroupoidsOver.exists_qcohRelativeLeraySpectralSequence :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z) (F : GroupoidsOver.QCoh X)
      [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
      [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g],
      ∃ (E : CohomologicalSpectralSequenceNat (GroupoidsOver.QCoh Z) 2)
        (pageTwoIso : ∀ p q : ℕ,
          (E.page 2 le_rfl).X (p, q) ≅ GroupoidsOver.qcohRelativeLerayPageTwo f g F p q),
        CohomologicalSpectralSequenceNat.ConvergesTo E
          (fun n ↦ GroupoidsOver.QCoh.higherDirectImage (f ≫ g) F n))

