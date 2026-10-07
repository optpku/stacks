module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Independence

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 48.32.1 -/
@[stacks 0G50]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.compactSupportPushforward_independent :
  ∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P Q : Scheme.Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)),
    IsIsomorphic
      (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.compactSupportPushforward f P)
      (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.compactSupportPushforward f Q))
