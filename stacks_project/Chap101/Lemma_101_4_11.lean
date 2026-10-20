/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Transfer
import StacksCheckRecall

/-!
# Transfer of separation axioms along morphisms of algebraic stacks

If a morphism of algebraic stacks is DM, quasi-DM, separated, or
quasi-separated, then the corresponding relative and absolute separation
axioms pass from the target to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.4.11 (1): if `Y` is DM over the base scheme and `f` is
DM, then `X` is DM over the base scheme. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsDMOver.of_DM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsDMOver Y] [DM f], IsDMOver X)

/- Lemma 101.4.11 (2): if `Y` is quasi-DM over the base scheme and `f` is
quasi-DM, then `X` is quasi-DM over the base scheme. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiDMOver.of_quasiDM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiDMOver Y] [QuasiDM f], IsQuasiDMOver X)

/- Lemma 101.4.11 (3): if `Y` is separated over the base scheme and `f` is
separated, then `X` is separated over the base scheme. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsSeparatedOver.of_separated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsSeparatedOver Y] [Separated f], IsSeparatedOver X)

/- Lemma 101.4.11 (4): if `Y` is quasi-separated over the base scheme and `f` is
quasi-separated, then `X` is quasi-separated over the base scheme. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparatedOver.of_quasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparatedOver Y] [QuasiSeparated f], IsQuasiSeparatedOver X)

/- Lemma 101.4.11 (5): if `Y` is DM and `f` is
DM, then `X` is DM. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsDM.of_DM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsDM Y] [DM f], IsDM X)

/- Lemma 101.4.11 (6): if `Y` is quasi-DM and `f` is
quasi-DM, then `X` is quasi-DM. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiDM.of_quasiDM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiDM Y] [QuasiDM f], IsQuasiDM X)

/- Lemma 101.4.11 (7): if `Y` is separated and `f` is
separated, then `X` is separated. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsSeparated.of_separated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsSeparated Y] [Separated f], IsSeparated X)

/- Lemma 101.4.11 (8): if `Y` is quasi-separated and `f` is
quasi-separated, then `X` is quasi-separated. -/
@[stacks 050L] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.of_quasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparated Y] [QuasiSeparated f], IsQuasiSeparated X)

end AlgebraicGeometry.AlgebraicStack
