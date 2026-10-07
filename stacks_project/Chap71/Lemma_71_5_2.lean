module

public import stacks_project.Chap71.Lemma_71_5_2_FittingIdeal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.5.2 (1) -/
@[stacks 0CZ5] #check
  (instIsQuasiCoherent_fittingIdealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ),
      (fittingIdealSheaf F i : X.Modules).IsQuasicoherent)

/- Lemma 71.5.2 (2) -/
@[stacks 0CZ5] #check
  (instIsFiniteType_fittingIdealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFinitePresentation] (r : ℕ),
      (fittingIdealSheaf F r : X.Modules).IsFiniteType)
