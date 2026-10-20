/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Opposites

/-!
# Comparison isomorphisms for reindexed inverse systems

This module owns the identity and composition comparison isomorphisms for
reindexing inverse systems.  It is independent of fiber smallness and colimit
assumptions.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w₀ w₁ w₂ v₀ v₁ v₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing

variable {C : Type u} [Category.{v} C]
variable {I : Type w₀} [Category.{v₀} I]
variable {I' : Type w₁} [Category.{v₁} I']

/-- The canonical inverse-system identification for reindexing along the identity functor. -/
noncomputable def idIso (S : Iᵒᵖ ⥤ C) :
    S ≅ (𝟭 I).op ⋙ S :=
  (Functor.leftUnitor S).symm

/-- The canonical comparison isomorphism for two successive reindexings. -/
noncomputable def compIso
    {I'' : Type w₂} [Category.{v₂} I'']
    {S : Iᵒᵖ ⥤ C} {T : I'ᵒᵖ ⥤ C} {U : I''ᵒᵖ ⥤ C}
    (j : I ⥤ I') (k : I' ⥤ I'') (e : S ≅ j.op ⋙ T) (e' : T ≅ k.op ⋙ U) :
    S ≅ (j ⋙ k).op ⋙ U :=
  e ≪≫ Functor.isoWhiskerLeft j.op e' ≪≫ Functor.associator j.op k.op U

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.Reindexing
