/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A nowhere dense closed subscheme with finite-normalization curve components on a
Noetherian regular surface becomes an effective Cartier divisor supported on a strict normal
crossings divisor after finitely many blowups in closed points. -/
theorem existsEffectiveCartierInverseImageWithStrictNormalCrossingsSupport
    (X : Scheme.{u}) [IsNoetherian X] [Regular X] (h_dim : topologicalKrullDim X = 2)
    (Z : X.IdealSheafData) (hZ : interior (closure Z.supportSet) = ∅)
    (h_components : ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (Z.subscheme.irreducibleComponentSubscheme C) = 1 →
        IsFinite (normalizationToOfIsNoetherian
          (Z.subscheme.irreducibleComponentSubscheme C))) :
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      IsEffectiveCartierDivisor (Z.comap s.toSource).subschemeι ∧
        ∃ (h_noetherian : IsLocallyNoetherian Xn) (D : Xn.IdealSheafData),
          @IsStrictNormalCrossingsDivisor Xn h_noetherian D ∧
            (Z.comap s.toSource).supportSet ⊆ D.supportSet := sorry

end AlgebraicGeometry.Scheme
