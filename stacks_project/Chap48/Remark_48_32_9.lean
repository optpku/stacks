/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FlatQuasiFinite.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.FlatQuasiFiniteCovariance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived.FlatQuasiFinite
open AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.FlatQuasiFiniteCovariance

universe u

/- Remark 48.32.9: covariance of compactly supported cohomology along a flat quasi-finite morphism. -/
@[stacks 0G58]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.FlatQuasiFiniteCovariance.comparison :
  ∀ {S : Scheme.{u}} [IsNoetherian S] {U X Y : Scheme.FiniteTypeSeparatedOver S}
    {h : U ⟶ X} [Flat h.hom.left] [Scheme.Hom.QuasiFinite h.hom.left] {f : X ⟶ Y}
    {C : AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice h f}
    (M : AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.FlatQuasiFiniteCovariance.Model h f C),
    AlgebraicGeometry.Scheme.ModuleDerived.FlatQuasiFinite.pullback h.hom.left ⋙
      M.compositePushforward ⟶ M.pushforward)
