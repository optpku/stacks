/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_14_2_Restriction
public import stacks_project.Chap103.Lemma_103_17_3_Instances

/-!
# Restriction of pullbacks to the small étale site of an algebraic space

A 1-morphism `f : U.toGroupoids ⟶ X` from an algebraic space yields the composite
functor sending an `𝒪_X`-module `F` to `f^* F` restricted to `U_étale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}

/-- The composite `f^* F |_{U_étale}`: pull back an `𝒪_X`-module along
`f : U.toGroupoids ⟶ X`, transport to the ring-valued étale ringed site of
`U.toGroupoids`, and restrict to the small étale site of `U`. -/
def restrictPullback (f : U.toGroupoids ⟶ X) :
    SheafOfModules.{u} (structureSheaf X) ⥤ AlgebraicSpace.Modules U :=
  modulePullback f ⋙ toEtaleRingedModules U.toGroupoids ⋙
    restrictModules (Bicategory.Equivalence.id U.toGroupoids)

/-- `restrictPullback f` is the composite of `modulePullback`, étale identity-on-Γ
transport, and `restrictModules` along the identity equivalence of `U.toGroupoids`. -/
theorem restrictPullback_eq (f : U.toGroupoids ⟶ X) :
    restrictPullback f =
      modulePullback f ⋙ toEtaleRingedModules U.toGroupoids ⋙
        restrictModules (Bicategory.Equivalence.id U.toGroupoids) :=
  rfl

/-- On objects, `restrictPullback f` sends `F` to the restriction of the étale
transport of `f^* F`. -/
theorem restrictPullback_obj (f : U.toGroupoids ⟶ X)
    (F : SheafOfModules.{u} (structureSheaf X)) :
    (restrictPullback f).obj F =
      (restrictModules (Bicategory.Equivalence.id U.toGroupoids)).obj
        ((toEtaleRingedModules U.toGroupoids).obj ((modulePullback f).obj F)) :=
  rfl

/-- Pullback along `f` followed by restriction to `U_étale` preserves quasi-coherence. -/
instance restrictPullback_isQuasicoherent (f : U.toGroupoids ⟶ X)
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent] :
    ((restrictPullback f).obj F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
