/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.InternalHom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Lemma 103.17.9: Let `X` be a locally Noetherian algebraic stack. Let `F` and `G`
be coherent `𝒪_X`-modules. Then the internal hom `hom(F, G)` constructed in
Lemma 103.10.8 is a coherent `𝒪_X`-module. -/
@[stacks 0GRD]
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_internalHomFP :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X]
    {F : fppfModules X} {G : QCoh X}
    [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G.obj],
    AlgebraicStack.IsCoherent (QCoh.internalHomFP F G).obj)
