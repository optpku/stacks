/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap109.Lemma_109_9_1_Substack
public import stacks_project.Chap109.Lemma_109_9_3_HigherDirectImage

/-!
# Higher direct images of the structure sheaf on families in 𝒞urves^{h0, 1}

If a family of curves has classifying morphism factoring through 𝒞urves^{h0, 1},
then 𝒪_S ⟶ f_* 𝒪_X is an isomorphism universally, R^1 f_* 𝒪_X is finite locally
free, and formation of that sheaf commutes with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.9.3 (1): if a family of curves has classifying morphism factoring
through 𝒞urves^{h0, 1}, then 𝒪_S ⟶ f_* 𝒪_X is an isomorphism after every base
change, including the identity. -/
@[stacks 0E1J]
theorem unitToPushforward_isIso_universally {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)) :
    IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g)) :=
  sorry

/-- Lemma 109.9.3 (2): if a family of curves has classifying morphism factoring
through 𝒞urves^{h0, 1}, then R^1 f_* 𝒪_X is a finite locally free 𝒪_S-module. -/
@[stacks 0E1J]
theorem higherDirectImageOne_isFiniteLocallyFree {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) :
    SheafOfModules.IsFiniteLocallyFree (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.9.3 (3): if a family of curves has classifying morphism factoring
through 𝒞urves^{h0, 1}, then formation of R^1 f_* 𝒪_X commutes with arbitrary
base change through the canonical comparison. -/
@[stacks 0E1J]
theorem higherDirectImageOne_commutesWithBaseChange {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)) :
    IsIso (higherDirectImageOneBaseChangeHom (hom P) g) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
