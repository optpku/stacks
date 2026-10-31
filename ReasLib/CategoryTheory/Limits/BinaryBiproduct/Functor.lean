/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise binary biproducts of functors

This leaf owns the comparison between the chosen binary biproduct in a functor category and the
pointwise binary biproduct in the target.  Keeping this comparison separate makes evaluation APIs
independent of unrelated colimit constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe uJ vJ uC vC

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable (F G : J ⥤ C)

/-- The chosen functor-category binary biproduct evaluates to the pointwise binary biproduct. -/
noncomputable def pointwiseBiprodIso :
    (pointwiseBinaryBicone F G).pt ≅ F ⊞ G :=
  biprod.uniqueUpToIso F G (pointwiseBinaryBicone.isBilimit F G)

/-- Evaluation of the chosen functor-category binary biproduct at `X`. -/
noncomputable def evalBiprodIso (X : J) :
    (F ⊞ G).obj X ≅ F.obj X ⊞ G.obj X :=
  ((pointwiseBiprodIso F G).app X).symm ≪≫
    eqToIso (pointwiseBinaryBicone_pt_obj F G X)

end CategoryTheory.Limits
