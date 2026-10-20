/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.RelativeResIsom
public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open FiberedCategoryOver.Groupoids

/- 97.12.5.1: the 2-fibre product
`(Sch/U)_fppf ×_{ξ × y, ℋ_d(𝒳) × 𝒴} ℋ_d(𝒳/𝒴)`.
`GroupoidsOver.slice U` is `(Sch/U)_fppf`; `ξ` is an object of `ℋ_d(𝒳)` over `U`
and `y` is an object of `𝒴` over `U`, represented as 1-morphisms by
`YonedaSlice.representative`; the product `ℋ_d(𝒳) × 𝒴` is the 2-fibre product of
the two `baseProjection` morphisms; `ξ × y` is `pairOverBase` of those
representatives; and the second leg is `pairOverBase` of the forgetful
1-morphisms `forgetToAbsolute F d` and `forgetToY F d`. -/
@[stacks 05YI] #check (AlgebraicGeometry.FiniteHilbertStack.relativeResIsom :
  {S : Scheme.{u}} →
  {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} →
  (F : 𝒳 ⟶ 𝒴) → (d : ℕ) → {U : Over S} →
  (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U) →
  (y : (asGroupoidsOver 𝒴).p.Fiber U) → GroupoidsOver S)
