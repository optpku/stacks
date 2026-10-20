/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Monoidal.Counit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.18.8

The reusable owner names the six arrows obtained from the derived-tensor counits, the derived
pullback counit, and the tensor comparison.  The chapter entry recalls their commutative square;
the generic total-left-derived construction and its compatibility with the 07A4 monoidal model
remain in `ReasLib`.
-/

/- Lemma 21.18.8 (0FPH): for complexes `K` and `M` of modules on the target ringed site, the
three-row diagram comparing derived pullback and derived tensor with ordinary totalized tensor
commutes. -/
@[stacks 0FPH "derived pullback tensor counit diagram"]
#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit.commSq

#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit.comparison
#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit.comparison_eq_monoidal
#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit.top
#check @RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit.bottom
