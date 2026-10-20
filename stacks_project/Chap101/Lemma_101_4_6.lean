/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.BaseChange
import StacksCheckRecall

/-!
# Change of base scheme for relative separation axioms

The properties of being quasi-DM, quasi-separated, or separated over a scheme
are stable under change of base scheme.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 101.4.6: Being quasi-DM, quasi-separated, or separated over a scheme
is stable under change of base scheme. -/
@[stacks 050G] #check
  (AlgebraicGeometry.AlgebraicStack.IsQuasiDMOver.of_baseChange :
    ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
      [AlgebraicStack X'] [IsQuasiDMOver X'],
      IsQuasiDMOver (baseChange g X'))

/- Lemma 101.4.6 (2): Quasi-separatedness over the base is stable under
change of base scheme. -/
@[stacks 050G] #check
  (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparatedOver.of_baseChange :
    ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
      [AlgebraicStack X'] [IsQuasiSeparatedOver X'],
      IsQuasiSeparatedOver (baseChange g X'))

/- Lemma 101.4.6 (3): Separatedness over the base is stable under change of
base scheme. -/
@[stacks 050G] #check
  (AlgebraicGeometry.AlgebraicStack.IsSeparatedOver.of_baseChange :
    ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
      [AlgebraicStack X'] [IsSeparatedOver X'],
      IsSeparatedOver (baseChange g X'))
