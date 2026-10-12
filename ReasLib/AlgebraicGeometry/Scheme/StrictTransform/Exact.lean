/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform

/-!
# Exactness of strict transforms

This file records exactness properties of strict transforms of quasicoherent module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The strict-transform functor preserves zero morphisms. -/
instance strictTransformFunctor_preservesZeroMorphisms
    {S S' X : Scheme.{u}} (b : S' ⟶ S) (E : S'.IdealSheafData) (f : X ⟶ S) :
    (strictTransformFunctor b E f).PreservesZeroMorphisms := sorry

namespace Scheme.Modules

/-- A quasicoherent short complex that is short exact after every base change remains short exact
after applying strict transform along a blowup. -/
theorem strictTransform_shortExact_of_forall_pullback_shortExact
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (S₀ : ShortComplex X.Modules)
    [S₀.X₁.IsQuasicoherent] [S₀.X₂.IsQuasicoherent] [S₀.X₃.IsQuasicoherent]
    (hbase : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      (S₀.map (Scheme.Modules.pullback (Limits.pullback.fst f t))).ShortExact) :
    (S₀.map (strictTransformFunctor b (I.comap b) f)).ShortExact := sorry

end Scheme.Modules

end AlgebraicGeometry
