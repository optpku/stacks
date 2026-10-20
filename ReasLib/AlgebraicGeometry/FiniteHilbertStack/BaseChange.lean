/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Square
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Base change of finite Hilbert stacks

A 2-cartesian square of stacks in groupoids induces a 2-cartesian square of
finite Hilbert stacks and their forgetful morphisms to the target stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.FiniteHilbertStack
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The pseudopullback cone with apex `H_d(𝒳'/𝒴')`, first leg `forgetToY F' d`,
second leg `AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d`, and bottom
cospan `H` and `forgetToY F d`. -/
def forgetToYSquare (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅
      AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d) :
    PseudoPullbackCone H (forgetToY F d) where
  pt := stack (toGroupoidsMor F') d
  fst := forgetToY F' d
  snd := AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d
  iso := comm

/-- The apex of `forgetToYSquare` is the finite Hilbert stack `H_d(𝒳'/𝒴')`. -/
theorem forgetToYSquare_pt (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅
      AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).pt = stack (toGroupoidsMor F') d :=
  rfl

/-- The first leg of `forgetToYSquare` is the forgetful 1-morphism
`H_d(𝒳'/𝒴') ⟶ 𝒴'`. -/
theorem forgetToYSquare_fst (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅
      AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).fst = forgetToY F' d :=
  rfl

/-- The second leg of `forgetToYSquare` is the induced 1-morphism
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)`. -/
theorem forgetToYSquare_snd (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅
      AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).snd =
      AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d :=
  rfl

/-- The comparison cell of `forgetToYSquare` is the supplied 2-isomorphism. -/
theorem forgetToYSquare_iso (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅
      AlgebraicGeometry.finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).iso = comm :=
  rfl

/-- A 2-cartesian square of stacks in groupoids remains 2-cartesian after applying
finite Hilbert stacks of degree `d` and their forgetful morphisms to the target stacks. -/
@[instance]
theorem forgetToYSquare_isBilimit (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    [PseudoPullbackCone.IsBilimit (⟨𝒳', F', G, γ⟩ : PseudoPullbackCone H F)] :
    (forgetToYSquare F' F G H γ d
        (eqToIso (finiteHilbertMapSquare_comp_forgetToY F' F G H γ d).symm)).IsBilimit :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
