/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth
import StacksCheckRecall

@[expose] public section

/-!
# A Jacobian-inverted standard smooth algebra

Example 10.137.7 adjoins a variable inverse to the selected Jacobian determinant.  The variable
order, relations, and quotient below retain the source presentation; standard smoothness is the
only derived statement kept in this file.

@stack 00T8
-/

open MvPolynomial

universe u

namespace Algebra

variable (R : Type u) [CommRing R]

/-- The variables occurring in the original equations. -/
@[stacks 00T8 "base variable indices"]
abbrev SmoothExampleBaseVars (c m : ℕ) : Type := Sum (Fin c) (Fin m)

/-- The source-prescribed order: selected variables, inverse variable, then remaining variables. -/
@[stacks 00T8 "reordered variable indices"]
abbrev SmoothExampleVars (c m : ℕ) : Type := Sum (Fin c) (Sum Unit (Fin m))

/-- The original relations together with the inverse-Jacobian relation. -/
@[stacks 00T8 "relation indices"]
abbrev SmoothExampleRelations (c : ℕ) : Type := Sum (Fin c) Unit

/-- The variable adjoining an inverse to the Jacobian determinant. -/
abbrev smoothExampleInverseVar (c m : ℕ) : SmoothExampleVars c m :=
  Sum.inr (Sum.inl ())

/-- Inclusion of the original variables into the source-prescribed order. -/
def smoothExampleBaseVarInclusion (c m : ℕ) :
    SmoothExampleBaseVars c m → SmoothExampleVars c m
  | Sum.inl i => Sum.inl i
  | Sum.inr i => Sum.inr (Sum.inr i)

/-- The determinant of the selected `c × c` Jacobian minor. -/
@[stacks 00T8 "Jacobian determinant"]
noncomputable def smoothExampleJacobian (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleBaseVars c m) R :=
  Matrix.det fun i j ↦ MvPolynomial.pderiv (Sum.inl i) (f j)

/-- The original equations followed by `Jacobian * inverseVar - 1`. -/
@[stacks 00T8 "defining relations"]
noncomputable def smoothExampleRelation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SmoothExampleRelations c → MvPolynomial (SmoothExampleVars c m) R
  | Sum.inl i => rename (smoothExampleBaseVarInclusion c m) (f i)
  | Sum.inr _ =>
      rename (smoothExampleBaseVarInclusion c m) (smoothExampleJacobian R c m f) *
        X (smoothExampleInverseVar c m) - 1

/-- The explicit quotient ring in Example 10.137.7. -/
@[stacks 00T8 "explicit quotient"]
noncomputable abbrev smoothExampleQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) : Type u :=
  MvPolynomial (SmoothExampleVars c m) R ⧸
    Ideal.span (Set.range (smoothExampleRelation R c m f))

/-- Example 10.137.7: adjoining the inverse-Jacobian relation gives a standard smooth algebra. -/
@[stacks 00T8]
theorem jacobian_inverted_quotient_isStandardSmooth (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsStandardSmooth R
      (MvPolynomial (SmoothExampleVars c m) R ⧸
        Ideal.span (Set.range (smoothExampleRelation R c m f))) := sorry

@[stacks 00T8 "canonical naive presentation"]
#check @PreSubmersivePresentation.naive

@[stacks 00T8 "canonical localization presentation"]
#check @SubmersivePresentation.localizationAway

@[stacks 00T8 "presentation-to-property bridge"]
#check @SubmersivePresentation.isStandardSmooth

end Algebra
