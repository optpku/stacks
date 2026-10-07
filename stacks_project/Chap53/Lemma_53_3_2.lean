module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries.Morphism

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 53.3.2 -/
@[stacks 0CCP] #check
  (AlgebraicGeometry.LinearSeries.exists_basisMorphismMapSpec :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
      [Scheme.Regular X.left] {d r : ℕ}
      (g : LinearSeries X (topologicalKrullDim_eq_one X).le d r),
        ∃ (b : Module.Basis (Fin (r + 1)) k g.sections)
          (φ : X ⟶ Over.mk (ProjectiveSpace.toSpec k r))
          (α : (Scheme.Modules.pullback φ.left).obj
              (ProjectiveSpace.twistingSheaf k r 1) ⟶
            g.lineBundle),
          ∀ i : Fin (r + 1),
            SheafOfModules.sectionsMap α
                (Scheme.Modules.sectionsPullback φ.left
                  (ProjectiveSpace.twistingSheaf k r 1)
                  (ProjectiveSpace.coordinateTwistSection k r i)) =
              RingedSpace.sectionFromTop g.lineBundle (g.inclusion (b i)))
