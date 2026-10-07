module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Coordinate

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSeries

/-- A linear series on a regular proper curve over a field is realized by a morphism to
projective space together with a map from the pulled-back degree-one twist to its line bundle,
carrying the homogeneous coordinates to a basis of the chosen section space. -/
theorem exists_basisMorphismMapSpec
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Scheme.Regular X.left] {d r : ℕ}
    (g : LinearSeries X (topologicalKrullDim_eq_one X).le d r) :
    ∃ (b : Module.Basis (Fin (r + 1)) k g.sections)
      (φ : X ⟶ Over.mk (ProjectiveSpace.toSpec k r))
      (α : (Scheme.Modules.pullback φ.left).obj
          (ProjectiveSpace.twistingSheaf k r 1) ⟶ g.lineBundle),
      ∀ i : Fin (r + 1),
        SheafOfModules.sectionsMap α
            (Scheme.Modules.sectionsPullback φ.left
              (ProjectiveSpace.twistingSheaf k r 1)
              (ProjectiveSpace.coordinateTwistSection k r i)) =
          RingedSpace.sectionFromTop g.lineBundle (g.inclusion (b i)) := sorry

end AlgebraicGeometry.LinearSeries
