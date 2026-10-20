/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Intersection
import StacksCheckRecall

/-!
# Lemma 29.4.5

Scheme-theoretic intersections as fiber products.

@stack 0C4I
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/- Lemma 29.4.5: the scheme-theoretic intersection of two closed subschemes is their fiber
product over the ambient scheme. -/
@[stacks 0C4I] #check
  (AlgebraicGeometry.schemeTheoreticIntersection_isPullback I J :
    IsPullback
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J))
      (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J))
      J.subschemeι
      I.subschemeι)

#check
  (inferInstance :
    IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J)))

#check
  (inferInstance :
    IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J)))

end AlgebraicGeometry
