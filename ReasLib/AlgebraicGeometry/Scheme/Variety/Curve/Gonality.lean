/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Lattice.Nat
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Model

/-!
# Gonality of a projective curve

The gonality of a projective curve `X` over `k` is the smallest degree of a
nonconstant morphism `X ⟶ ℙ¹_k`, realized as the infimum of function-field
degrees of dominant finite morphisms over `k` to `ProjectiveSpace.schemeOver k 1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- The function-field degree of a dominant morphism to `ℙ¹` over `k`. -/
noncomputable def degreeToProjectiveLine {k : Type u} [Field k]
    {X : SchemeOverField k} [IsIntegral X.left]
    (φ : X ⟶ ProjectiveSpace.schemeOver k 1)
    (hdom : IsDominant φ.left) : ℕ :=
  @Scheme.Hom.inducedFunctionFieldDegree _ _ φ.left inferInstance inferInstance hdom

/-- Finiteness of the function-field extension induced by a dominant morphism to `ℙ¹`. -/
def FiniteDegreeToProjectiveLine {k : Type u} [Field k]
    {X : SchemeOverField k} [IsIntegral X.left]
    (φ : X ⟶ ProjectiveSpace.schemeOver k 1)
    (hdom : IsDominant φ.left) : Prop :=
  @Scheme.Hom.FiniteFunctionFieldExtension _ _ φ.left inferInstance inferInstance hdom

/-- A finite dominant morphism to `ℙ¹` has positive function-field degree. -/
theorem degreeToProjectiveLine_pos {k : Type u} [Field k]
    {X : SchemeOverField k} [IsIntegral X.left]
    (φ : X ⟶ ProjectiveSpace.schemeOver k 1)
    (hdom : IsDominant φ.left)
    (hfin : FiniteDegreeToProjectiveLine φ hdom) :
    0 < degreeToProjectiveLine φ hdom := sorry

/-- Degrees of dominant finite morphisms from a projective curve to `ℙ¹_k`. -/
def gonalitySet {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] : Set ℕ :=
  {d | ∃ (φ : X ⟶ ProjectiveSpace.schemeOver k 1) (hdom : IsDominant φ.left)
      (_ : FiniteDegreeToProjectiveLine φ hdom),
      degreeToProjectiveLine φ hdom = d}

/-- Membership in `gonalitySet` is existence of a dominant finite map to `ℙ¹` of that degree. -/
theorem mem_gonalitySet_iff {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] {d : ℕ} :
    d ∈ gonalitySet X ↔
      ∃ (φ : X ⟶ ProjectiveSpace.schemeOver k 1) (hdom : IsDominant φ.left)
        (hfin : FiniteDegreeToProjectiveLine φ hdom),
        degreeToProjectiveLine φ hdom = d := sorry

/-- The gonality of a projective curve is the smallest degree of a nonconstant morphism
to `ℙ¹_k`. -/
noncomputable def gonality {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] : ℕ :=
  sInf (gonalitySet X)

/-- Gonality is the infimum of degrees of dominant finite morphisms to `ℙ¹_k`. -/
theorem gonality_def {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] :
    gonality X = sInf (gonalitySet X) := sorry

/-- A projective curve admits at least one dominant finite morphism to `ℙ¹_k`. -/
theorem exists_mem_gonalitySet {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] : (gonalitySet X).Nonempty := sorry

/-- Gonality is at most `n` if and only if there is a dominant finite morphism to `ℙ¹`
of degree at most `n`. -/
theorem gonality_le_iff {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] {n : ℕ} :
    gonality X ≤ n ↔
      ∃ (φ : X ⟶ ProjectiveSpace.schemeOver k 1) (hdom : IsDominant φ.left)
        (hfin : FiniteDegreeToProjectiveLine φ hdom),
        degreeToProjectiveLine φ hdom ≤ n := sorry

end AlgebraicGeometry.Curve

namespace AlgebraicGeometry.NonsingularProjectiveModel.WithIso

/-- The gonality of a nonsingular projective model, computed on its underlying
projective curve. -/
noncomputable def gonality {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (Y : WithIso X) : ℕ :=
  @Curve.gonality k _ Y.curve Y.isCurve Y.projective

/-- Model gonality is the curve gonality of the underlying projective curve. -/
theorem gonality_def {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (Y : WithIso X) :
    Y.gonality = @Curve.gonality k _ Y.curve Y.isCurve Y.projective := sorry

end AlgebraicGeometry.NonsingularProjectiveModel.WithIso
