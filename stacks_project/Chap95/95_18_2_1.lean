/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.«95_18_2_1_Stack»
public import stacks_project.Chap95.«95_18_2_1_Forgetful»

/-!
# Equation 95.18.2.1

The four forgetful 1-morphisms of finite Hilbert stacks over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- 95.18.2.1 (1) The forgetful 1-morphism `H_d(𝒳) ⟶ H_d` of stacks in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 05WD]
def finiteHilbertAbsoluteToPoint {S : Scheme.{u}}
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ) :
    ofStack 𝒳.toGroupoids d ⟶ ofScheme S d :=
  absoluteToPoint 𝒳 d

/-- 95.18.2.1 (2) The forgetful 1-morphism `H_d(𝒳/𝒴) ⟶ H_d` of stacks in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 05WD]
def finiteHilbertForgetToPoint {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    stack (toGroupoidsMor F) d ⟶ ofScheme S d :=
  forgetToPoint F d

/-- 95.18.2.1 (3) The forgetful 1-morphism `H_d(𝒳/𝒴) ⟶ H_d(𝒳)` of stacks in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 05WD]
def finiteHilbertForgetToAbsolute {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    stack (toGroupoidsMor F) d ⟶ ofStack 𝒳.toGroupoids d :=
  forgetToAbsolute F d

/-- 95.18.2.1 (4) The forgetful 1-morphism `H_d(𝒳/𝒴) ⟶ 𝒴` of stacks in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 05WD]
def finiteHilbertForgetToY {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    stack (toGroupoidsMor F) d ⟶ 𝒴 :=
  forgetToY F d

/-- The labeled triangle `H_d(𝒳/𝒴) ⟶ H_d(𝒳) ⟶ H_d` agrees with `H_d(𝒳/𝒴) ⟶ H_d`. -/
theorem finiteHilbertForgetToAbsolute_comp_absoluteToPoint {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    finiteHilbertForgetToAbsolute F d ≫ finiteHilbertAbsoluteToPoint 𝒳 d =
      finiteHilbertForgetToPoint F d :=
  sorry

end AlgebraicGeometry
