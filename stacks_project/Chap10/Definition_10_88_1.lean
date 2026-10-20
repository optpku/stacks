/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler
import StacksCheckRecall

@[expose] public section

/-!
# Mittag-Leffler directed systems of modules

Definition 10.88.1: a directed system `(M_i, f_ij)` of `R`-modules is a Mittag-Leffler
directed system if each `M_i` is finitely presented and, for every `R`-module `N`, the
inverse system `(Hom_R(M_i, N), Hom_R(f_ij, N))` is Mittag-Leffler.

The reusable owner is `Module.IsMittagLefflerDirectedSystem` on a directed
`I ⥤ ModuleCat R`.  The Hom inverse system named in the source is
`CategoryTheory.Functor.homInverseSystem`.

@stack 059A
-/

open CategoryTheory

universe u v w

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/- Definition 10.88.1: a directed system of `R`-modules is Mittag-Leffler when every
stage is finitely presented and every Hom inverse system is Mittag-Leffler. -/
@[stacks 059A]
#check (Module.IsMittagLefflerDirectedSystem : (I ⥤ ModuleCat.{w} R) → Prop)

#check (Module.IsMittagLefflerDirectedSystem.finitePresentation :
  ∀ {diagram : I ⥤ ModuleCat.{w} R}, Module.IsMittagLefflerDirectedSystem diagram →
    ∀ index : I, Module.FinitePresentation R (diagram.obj index))

#check (Module.IsMittagLefflerDirectedSystem.homMittagLeffler :
  ∀ {diagram : I ⥤ ModuleCat.{w} R}, Module.IsMittagLefflerDirectedSystem diagram →
    diagram.HomMittagLeffler)

#check (CategoryTheory.Functor.homInverseSystem :
  (I ⥤ ModuleCat.{w} R) → ModuleCat.{w} R → (Iᵒᵖ ⥤ Type w))
