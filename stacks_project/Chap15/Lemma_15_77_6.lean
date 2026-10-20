/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Ext
import StacksCheckRecall

/-!
# Lemma 15.77.6

@stack 0G98
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory

variable {R : Type u} [Ring R]
variable (K : DerivedCategory.Minus (ModuleCat R)) (a : ℤ)
variable (hExt : IsZero (DerivedCategory.Ext.addCommGrpFunctor K.obj (-a)))

/- Lemma 15.77.6: vanishing of `Ext^{-a}_R(K, -)` gives projective amplitude for `τ≥ a + 1`
and the unique compatible gap decomposition `K ≅ τ≤ a - 1 K ⊞ τ≥ a + 1 K`. -/
@[stacks 0G98 "Ext vanishing and gap truncation splitting"]
#check
  (DerivedCategory.ProjectiveAmplitude.existsUnique_truncationGapBiprod_of_ext_isZero K a hExt :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE (a - 1)).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι (a - 1)).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj))

#check @DerivedCategory.Ext.addCommGrpFunctor

end CategoryTheory
