/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
import StacksCheckRecall

/-!
# Lemma 29.4.6

The structure-sheaf Mayer–Vietoris sequence and pushout property of a scheme-theoretic union.

@stack 0C4J
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.4.6: closed subschemes form a Mayer–Vietoris sequence whose square is a pushout. -/
@[stacks 0C4J] #check
  (AlgebraicGeometry.schemeTheoreticUnion_structureSheaf_shortExact :
    ∀ {S : Scheme.{u}} (I J : S.IdealSheafData),
      (AlgebraicGeometry.schemeTheoreticUnionShortComplex I J).ShortExact)

variable {S : Scheme.{u}} (I J : S.IdealSheafData)

#check (AlgebraicGeometry.schemeTheoreticUnionShortComplex I J : ShortComplex S.Modules)

#check (inferInstance :
  IsClosedImmersion
    (Scheme.IdealSheafData.inclusion (inf_le_left : I ⊓ J ≤ I) :
      I.subscheme ⟶ Scheme.schemeTheoreticUnion I J))

#check (inferInstance :
  IsClosedImmersion
    (Scheme.IdealSheafData.inclusion (inf_le_right : I ⊓ J ≤ J) :
      J.subscheme ⟶ Scheme.schemeTheoreticUnion I J))

#check (AlgebraicGeometry.schemeTheoreticUnion_isPushout I J :
  IsPushout
    (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) :
      Scheme.schemeTheoreticIntersection I J ⟶ I.subscheme)
    (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) :
      Scheme.schemeTheoreticIntersection I J ⟶ J.subscheme)
    (Scheme.IdealSheafData.inclusion (inf_le_left : I ⊓ J ≤ I) :
      I.subscheme ⟶ Scheme.schemeTheoreticUnion I J)
    (Scheme.IdealSheafData.inclusion (inf_le_right : I ⊓ J ≤ J) :
      J.subscheme ⟶ Scheme.schemeTheoreticUnion I J))
