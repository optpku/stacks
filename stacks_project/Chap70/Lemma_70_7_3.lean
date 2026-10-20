/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Limit.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Limit.Invertible
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 70.7.3 (1): a finite locally free module on a directed inverse limit of
quasi-compact, absolutely quasi-separated algebraic spaces with affine transition maps descends
to a finite locally free module at some stage. -/
@[stacks 0D2X] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FiniteLocallyFree.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (ℱ : c.pt.Modules) [ℱ.IsFiniteLocallyFree],
      ∃ (i : I) (ℱi : (D.obj i).Modules),
        ℱi.IsFiniteLocallyFree ∧
          Nonempty ((Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ))

/- Lemma 70.7.3 (2): an invertible module on a directed inverse limit of
quasi-compact, absolutely quasi-separated algebraic spaces with affine transition maps descends
to an invertible module at some stage. -/
@[stacks 0D2X] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Limit.Invertible.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (ℒ : c.pt.Modules) [isInvertibleObject ℒ],
      ∃ (i : I) (ℒi : (D.obj i).Modules),
        isInvertibleObject ℒi ∧
          Nonempty ((Modules.pullback (c.π.app i)).obj ℒi ≅ ℒ))
