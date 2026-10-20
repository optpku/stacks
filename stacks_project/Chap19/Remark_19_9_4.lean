/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.SmallSubcategory
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory

/- Remark 19.9.4 (1): any set-sized family of objects in a possibly large abelian category is
contained in a small abelian full subcategory whose inclusion is exact.  This lets diagram-chase
arguments be carried out in the small subcategory and transported back to the ambient category. -/
@[stacks 05PQ] #check
  fun (A : Type u) [Category.{v} A] [Abelian A]
      (E : ObjectProperty A) [ObjectProperty.Small.{w} E] ↦
    (SmallAbelianSubcategory.exists_containing E :
      ∃ B : SmallAbelianSubcategory.{max v w, v, u} A, B.Contains E)

/- Remark 19.9.4 (2): exactness of a short complex can be checked before or after the inclusion,
which is the bridge used to transport diagram chases back to the ambient category. -/
@[stacks 05PQ "short exact transport"] #check
  fun (A : Type u) [Category.{v} A] [Abelian A]
      (B : SmallAbelianSubcategory.{w, v, u} A)
      (S : ShortComplex B.FullSubcategory) ↦
    (B.inclusion_shortExact_iff (S := S) :
      (S.map B.carrier.ι).ShortExact ↔ S.ShortExact)

end CategoryTheory
