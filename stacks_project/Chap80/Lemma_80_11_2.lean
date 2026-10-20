/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfLocal
import StacksCheckRecall

/-!
# Fppf locality of algebraic spaces of finite type

A sheaf which is fppf locally an algebraic space of finite type over the
cover is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

/- Lemma 80.11.2: an fppf sheaf locally represented by algebraic spaces of
finite type over an fppf covering is an algebraic space. -/
@[stacks 04U0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_fppfLocal_finiteType :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
      (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {I : Type v}
      (Si : I → Over S) (hSi : Scheme.FppfCovering Si)
      (hFi : ∀ i, AlgebraicSpace.IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F))
      (h_finiteType : ∀ i, AlgebraicSpace.FiniteType (AlgebraicSpace.yonedaProdFst (hFi i))),
      AlgebraicSpace.IsAlgebraicSpace F)
