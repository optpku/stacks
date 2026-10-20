/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Category.ModuleCat.Descent.BaseChangeLimit

@[expose] public section

universe u

/- Remark 35.4.21 (1): if `Algebra.linearMap R S` has an explicit `R`-linear
retraction, then extending scalars to `S` carries the descent-pushforward equalizer
fork to a limiting fork. -/
@[stacks 08X9] #check
  (ModuleCat.DescentPushforward.baseChangeIsLimit_of_retraction :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
      (r : S →ₗ[R] R) (h_r : r.comp (Algebra.linearMap R S) = LinearMap.id)
      (D : (ModuleCat.extendRestrictScalarsAdj.{u}
        (algebraMap R S)).toComonad.Coalgebra),
      Nonempty (CategoryTheory.Limits.IsLimit
        (ModuleCat.DescentPushforward.baseChangeFork (algebraMap R S) D)))

/- Remark 35.4.21 (2): if `algebraMap R S` is faithfully flat, then extending
scalars to `S` carries the descent-pushforward equalizer fork to a limiting fork. -/
@[stacks 08X9] #check
  (ModuleCat.DescentPushforward.baseChangeIsLimit_of_faithfullyFlat :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
      (h_f : (algebraMap R S).FaithfullyFlat)
      (D : (ModuleCat.extendRestrictScalarsAdj.{u}
        (algebraMap R S)).toComonad.Coalgebra),
      Nonempty (CategoryTheory.Limits.IsLimit
        (ModuleCat.DescentPushforward.baseChangeFork (algebraMap R S) D)))
