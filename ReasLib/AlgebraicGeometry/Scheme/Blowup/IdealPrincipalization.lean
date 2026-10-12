/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequenceSupport
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A finitely supported ideal on a Noetherian scheme with regular two-dimensional local rings at
the support becomes effective Cartier after finitely many point blowups over that support. -/
theorem existsInvertibleIdealAfterPointBlowups
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X)
    (hT_finite : T.Finite) (hT_closed : T ⊆ closedPoints X)
    (hT_regular : ∀ x, x ∈ T → IsRegularLocalRing (X.presheaf.stalk x))
    (hT_dimension : ∀ x, x ∈ T → ringKrullDim (X.presheaf.stalk x) = 2)
    (I : X.IdealSheafData) (hI_support : I.supportSet ⊆ T) :
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      s.EveryCenterOver T ∧
        IsEffectiveCartierDivisor ((I.comap s.toSource).subschemeι) := sorry

/-- A closed subscheme with nowhere dense support on a Noetherian regular scheme of dimension
two becomes an effective Cartier divisor after finitely many blowups at closed points. -/
theorem existsEffectiveCartierInverseImageAfterPointBlowups
    (X : Scheme.{u}) [IsNoetherian X] [Regular X] (h_dim : topologicalKrullDim X = 2)
    (Z : X.IdealSheafData) (hZ : interior (closure Z.supportSet) = ∅) :
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      IsEffectiveCartierDivisor (Z.comap s.toSource).subschemeι := sorry

end AlgebraicGeometry.Scheme
