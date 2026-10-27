/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.LimitPreserving

/-!
# Lemma 99.16.8

In Situation 99.16.3, if `B` is locally of finite presentation over `S`, the
projection of the category of complexes is limit preserving. Its fibre
Hom-diagrams take values in `Type (u + 1)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Complexes

universe u

/- Lemma 99.16.8: for a proper, flat morphism of finite presentation, if `B`
is locally of finite presentation over `S`, the projection from relatively
perfect complexes with vanishing negative fibre self-Ext is limit preserving
in the sense of Artin's Axioms, Definition 98.11.1. -/
@[stacks 0DLJ] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.isLimitPreserving :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (SchemeRealization.toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left),
    (∀ x : (p f).Fiber c.pt, ∃ (i : I) (xi : (p f).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (p f).Fiber (D.obj i)),
        Nonempty (IsColimit (CategoryTheory.Functor.Fiber.DirectedSystem.homCocone
          (p f) c x y)))
