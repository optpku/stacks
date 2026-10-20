module

public import ReasLib.AlgebraicGeometry.Scheme.Size.Fpqc
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

/- Lemma 3.9.11: an fpqc covering of `Y` whose arrows factor through
`f : X ⟶ Y` implies `Y.size ≤ X.size`. -/
@[stacks 0AHK] #check
  (AlgebraicGeometry.Scheme.size_le_of_fpqcCovering_factors :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v}
      (Yj : ι → Scheme.{u}) (g : (j : ι) → Yj j ⟶ Y)
      (hg : Presieve.ofArrows Yj g ∈ Scheme.fpqcPrecoverage Y)
      (hfactor : ∀ j, ∃ h : Yj j ⟶ X, h ≫ f = g j),
      Y.size ≤ X.size)
