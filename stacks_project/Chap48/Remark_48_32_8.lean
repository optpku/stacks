/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.EtaleCovariance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived.Etale
open AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.EtaleCovariance

universe u

/- Remark 48.32.8: étale covariance of compactly supported cohomology. -/
@[stacks 0G57]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.EtaleCovariance.comparison :
  ∀ {S : Scheme.{u}} [IsNoetherian S] {U X Y : Scheme.FiniteTypeSeparatedOver S}
    {h : U ⟶ X} [AlgebraicGeometry.Etale h.hom.left] {f : X ⟶ Y}
    {C : AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice h f}
    (M : AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.EtaleCovariance.Model h f C),
    AlgebraicGeometry.Scheme.ModuleDerived.Etale.pullback h.hom.left ⋙ M.compositePushforward ⟶ M.pushforward)
