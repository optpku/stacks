/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries.Quadrics
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.56.9: a complete linear series of sufficiently large degree relative to the
genus of a regular proper curve over an algebraically closed field has image contained in a
nonzero quadric. The bound `2 * SchemeOverField.genus C (topologicalKrullDim_eq_one C) hΓ + 2 ≤ d`
is sufficient and is not asserted to be optimal. -/
@[stacks 09U4] #check
  (AlgebraicGeometry.LinearSeries.exists_quadric_of_complete :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (C : SchemeOverField k) [Curve C] [IsProper C.hom] [Scheme.Regular C.left]
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) (d r : ℕ)
      (g : LinearSeries C (topologicalKrullDim_eq_one C).le d r),
      g.sections = ⊤ →
        2 * SchemeOverField.genus C (topologicalKrullDim_eq_one C) hΓ + 2 ≤ d →
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
                  AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.liesOnHypersurface
                    r φ.left.ker F)

end
