/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal

/-!
# Exceptional curves of the first kind

This module records the geometric hypothesis used by contraction arguments: an effective
Cartier divisor is a projective line whose normal sheaf is `𝒪(-1)`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- An ideal sheaf defines an exceptional curve of the first kind when its closed subscheme is
an effective Cartier divisor isomorphic to a projective line, with normal sheaf pulling back to
the twisting sheaf `𝒪(-1)`. -/
class IsExceptionalCurveFirstKind {X : Scheme.{u}} (E : X.IdealSheafData) : Prop
    extends IsEffectiveCartierDivisor E.subschemeι where
  /-- A projective-line presentation on which the normal sheaf is `𝒪(-1)`. -/
  projectiveLineNormal :
    ∃ (k : Type u) (_ : Field k) (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme),
      IsIsomorphic
        ((Scheme.Modules.pullback e.hom).obj (Scheme.Hom.normalSheaf E.subschemeι))
        (ProjectiveSpace.twistingSheaf k 1 (-1))

/-- An exceptional curve of the first kind is canonically an effective Cartier divisor. -/
instance IsExceptionalCurveFirstKind.instIsEffectiveCartierDivisor
    {X : Scheme.{u}} (E : X.IdealSheafData) [hE : IsExceptionalCurveFirstKind E] :
    IsEffectiveCartierDivisor E.subschemeι :=
  hE.toIsEffectiveCartierDivisor

/-- The effective-Cartier and projective-line normal-sheaf conditions characterize exceptional
curves of the first kind. -/
theorem isExceptionalCurveFirstKind_iff {X : Scheme.{u}} (E : X.IdealSheafData) :
    IsExceptionalCurveFirstKind E ↔
      IsEffectiveCartierDivisor E.subschemeι ∧
        ∃ (k : Type u) (_ : Field k) (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme),
          IsIsomorphic
            ((Scheme.Modules.pullback e.hom).obj (Scheme.Hom.normalSheaf E.subschemeι))
            (ProjectiveSpace.twistingSheaf k 1 (-1)) := sorry

end AlgebraicGeometry
