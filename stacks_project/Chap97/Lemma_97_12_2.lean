/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

universe u

/- Lemma 97.12.2: a 2-cartesian square of stacks in groupoids induces a
2-cartesian square of finite Hilbert stacks and their forgetful morphisms. -/
@[stacks 05XP] #check (AlgebraicGeometry.FiniteHilbertStack.forgetToYSquare_isBilimit :
  {S : Scheme.{u}} →
  {𝒳' 𝒳 𝒴' 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u}
    (Scheme.fppfTopology.over S)} →
  (F' : 𝒳' ⟶ 𝒴') → (F : 𝒳 ⟶ 𝒴) → (G : 𝒳' ⟶ 𝒳) → (H : 𝒴' ⟶ 𝒴) →
  (γ : F' ≫ H ≅ G ≫ F) → (d : ℕ) →
  [PseudoPullbackCone.IsBilimit (⟨𝒳', F', G, γ⟩ : PseudoPullbackCone H F)] →
  (forgetToYSquare F' F G H γ d
    (eqToIso (finiteHilbertMapSquare_comp_forgetToY F' F G H γ d).symm)).IsBilimit)
