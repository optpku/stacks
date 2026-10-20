/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.Limits
import StacksCheckRecall

/-!
# Lemma 12.32.1

The reusable owner is stated for arbitrary exact limits. This source file records the product
specialization and its projection formula without exposing the implementation through the
short-complex/functor-category equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type u'} [Category.{v'} J]
variable [HasLimitsOfShape J C] [HasExactLimitsOfShape J C]
variable (S : J ⥤ ShortComplex C) (j : J)

/- Lemma 12.32.1 [060K]: exact products commute with the homology of short complexes. -/
@[stacks 060K]
#check (ShortComplex.LimitHomology.iso S :
  (limit S).homology ≅ limit (S ⋙ ShortComplex.homologyFunctor C))

/- The comparison is usable componentwise without unfolding its concrete construction. -/
#check (ShortComplex.LimitHomology.iso_hom_π S j :
  (ShortComplex.LimitHomology.iso S).hom ≫
      limit.π (S ⋙ ShortComplex.homologyFunctor C) j =
    ShortComplex.homologyMap (limit.π S j))

/- The shared owner is formulated at the mathematically natural arbitrary-limit level. -/
section Products

variable {I : Type v'} [HasProductsOfShape I C]
  [HasExactLimitsOfShape (Discrete I) C]
variable (P : I → ShortComplex C) (i : I)

#check (ShortComplex.PiHomology.iso P :
  (∏ᶜ P).homology ≅ ∏ᶜ fun i ↦ (P i).homology)
#check (ShortComplex.PiHomology.iso_hom_π P i :
  (ShortComplex.PiHomology.iso P).hom ≫ Pi.π (fun j ↦ (P j).homology) i =
    ShortComplex.homologyMap (Pi.π P i))

end Products

/- The arbitrary-limit comparison is likewise characterized by its projections. -/
