/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Square
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic

/-!
# Étale morphisms of finite Hilbert stacks

For positive degree, a 2-commutative square whose horizontal morphisms are
representable by algebraic spaces and étale induces a representable étale
morphism of finite Hilbert stacks. It is surjective when the bottom morphism
and the canonical comparison to the two-fibre product are surjective.
The identity-base specializations are also provided.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- A representable étale morphism in an identity-base square induces a
representable étale morphism of finite Hilbert stacks of positive degree. -/
instance _root_.AlgebraicGeometry.finiteHilbertMapSquare.etale (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ) [NeZero d]
    [Etale (asGroupoidsOverMor G)] :
    Etale
      (asGroupoidsOverMor (finiteHilbertMapSquare F' F G (𝟙 𝒴) γ d)) :=
  sorry

/-- A representable étale surjection in an identity-base square induces a
surjective morphism of finite Hilbert stacks of positive degree. -/
instance _root_.AlgebraicGeometry.finiteHilbertMapSquare.surjective (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ) [NeZero d]
    [Etale (asGroupoidsOverMor G)]
    [Surjective (asGroupoidsOverMor G)] :
    Surjective
      (asGroupoidsOverMor (finiteHilbertMapSquare F' F G (𝟙 𝒴) γ d)) :=
  sorry

variable {𝒴' :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- A 2-commutative square with representable étale horizontal morphisms induces
a representable étale morphism of finite Hilbert stacks of positive degree. -/
instance _root_.AlgebraicGeometry.finiteHilbertMapSquare.etaleOfSquare
    (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) [NeZero d]
    [Etale (asGroupoidsOverMor G)]
    [Etale (asGroupoidsOverMor H)] :
    Etale (asGroupoidsOverMor (finiteHilbertMapSquare F' F G H γ d)) :=
  sorry

/-- A 2-commutative square with representable étale horizontal morphisms induces
a surjective morphism of finite Hilbert stacks of positive degree if its bottom
morphism and canonical comparison to the two-fibre product are surjective. -/
instance _root_.AlgebraicGeometry.finiteHilbertMapSquare.surjectiveOfSquare
    (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) [NeZero d]
    [Etale (asGroupoidsOverMor G)]
    [Etale (asGroupoidsOverMor H)]
    [Surjective (asGroupoidsOverMor H)]
    [Surjective (asGroupoidsOverMor
      (CategoryTheory.Bicategory.PseudoPullbackCone.lift
        (CategoryTheory.Bicategory.PseudoPullbackCone.mk H F 𝒳' F' G γ)
        (CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u}
          H F)))] :
    Surjective (asGroupoidsOverMor (finiteHilbertMapSquare F' F G H γ d)) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
