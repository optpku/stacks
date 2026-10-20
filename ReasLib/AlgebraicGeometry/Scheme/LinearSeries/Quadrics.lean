module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Coordinate
public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSeries

open ProjectiveSpace.ClosedSubscheme

/-- A complete linear series of degree at least twice the genus plus two on a regular proper curve
over an algebraically closed field has a quadratic equation for every compatible projective map. -/
theorem exists_quadric_of_complete
    {k : Type u} [Field k] [IsAlgClosed k]
    (C : SchemeOverField k) [Curve C] [IsProper C.hom] [Scheme.Regular C.left]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (d r : ℕ) (g : LinearSeries C (topologicalKrullDim_eq_one C).le d r)
    (hcomplete : g.sections = ⊤)
    (hdegree : 2 * SchemeOverField.genus C (topologicalKrullDim_eq_one C) hΓ + 2 ≤ d) :
    ∀ (b : Module.Basis (Fin (r + 1)) k g.sections)
      (φ : C ⟶ Over.mk (ProjectiveSpace.toSpec k r))
      (α : (Scheme.Modules.pullback φ.left).obj
          (ProjectiveSpace.twistingSheaf k r 1) ⟶ g.lineBundle),
      (∀ i : Fin (r + 1),
          SheafOfModules.sectionsMap α
              (Scheme.Modules.sectionsPullback φ.left
                (ProjectiveSpace.twistingSheaf k r 1)
                (ProjectiveSpace.coordinateTwistSection k r i)) =
            RingedSpace.sectionFromTop g.lineBundle (g.inclusion (b i))) →
        ∃ F : MvPolynomial (Fin (r + 1)) k,
          F ∈ ProjectiveSpace.grading k r 2 ∧ F ≠ 0 ∧
            liesOnHypersurface r φ.left.ker F := sorry

end AlgebraicGeometry.LinearSeries
