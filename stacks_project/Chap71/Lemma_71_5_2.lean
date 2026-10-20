module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.5.2 (1) -/
@[stacks 0CZ5] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf.instIsQuasicoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ),
      (fittingIdealSheaf F i : X.Modules).IsQuasicoherent)

/- Lemma 71.5.2 (2) -/
@[stacks 0CZ5] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsFiniteType_fittingIdealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFinitePresentation] (r : ℕ),
      (fittingIdealSheaf F r : X.Modules).IsFiniteType)
