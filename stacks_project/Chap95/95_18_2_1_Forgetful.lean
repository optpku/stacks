/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful

/-!
# Forgetful morphisms of finite Hilbert stacks

Canonical forgetful morphisms and their commuting triangle.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

universe u

#check (AlgebraicGeometry.FiniteHilbertStack.absoluteToPoint :
  ∀ {S : Scheme.{u}} (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ),
    ofStack 𝒳.toGroupoids d ⟶ ofScheme S d)

#check (AlgebraicGeometry.FiniteHilbertStack.forgetToPoint :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    stack (StackOver.Groupoids.Hom.toGroupoidsMor F) d ⟶ ofScheme S d)

#check (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    stack (StackOver.Groupoids.Hom.toGroupoidsMor F) d ⟶ ofStack 𝒳.toGroupoids d)

#check (AlgebraicGeometry.FiniteHilbertStack.forgetToY :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    stack (StackOver.Groupoids.Hom.toGroupoidsMor F) d ⟶ 𝒴)

#check (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute_comp_absoluteToPoint :
  ∀ {S : Scheme.{u}} {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴) (d : ℕ),
    AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute F d ≫
      AlgebraicGeometry.FiniteHilbertStack.absoluteToPoint 𝒳 d =
        AlgebraicGeometry.FiniteHilbertStack.forgetToPoint F d)
