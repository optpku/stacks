/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedAlgebraSections
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Quadruple

/-!
# Affine representability of fixed-degree relative projective functors

Over an affine base, the functor associated to fixed-degree relative projective quadruples is
represented by the corresponding fixed-degree open in the projective spectrum of the graded
global-section ring.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
variable (d : ℕ)

/-- An affine fixed-degree relative projective functor associated to quadruples is represented
by the degree-`d` open of the projective spectrum of its graded global sections. -/
theorem isRepresentedByTopSectionsDegreeOpen
    [𝒜.IsCommutative] [IsAffine S]
    (F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (associatedToQuadruples : F_d.IsAssociatedToQuadruples) :
    ∃ x : F_d.toFunctor.obj
        (op (Proj.degreeOpen (RingedSpace.GradedAlgebraSections.grading 𝒜) d).toScheme),
      F_d.toFunctor.IsRepresentedBy x := sorry

end AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor
