/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import StacksCheckRecall

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Abelian Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D]
variable {S : ShortComplex C} (hS : S.ShortExact)

/- Lemma 12.7.3 [010O] (1): an exact functor induces an additive
homomorphism on every Ext group, in particular in degree one. -/
@[stacks 010O]
#check (F.mapExtAddHom S.X₃ S.X₁ 1 :
  Ext S.X₃ S.X₁ 1 →+ Ext (F.obj S.X₃) (F.obj S.X₁) 1)

/- Lemma 12.7.3 [010O] (2): in degree one, the induced map sends the
class of a short exact sequence to the class of its image. -/
@[stacks 010O]
#check (Abelian.Ext.mapExactFunctor_extClass F hS :
  Abelian.Ext.mapExactFunctor F hS.extClass = (hS.map_of_exact F).extClass)

end CategoryTheory
