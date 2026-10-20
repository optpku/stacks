/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Preadditive ℬ]
  [HasZeroObject 𝒜] [HasZeroObject ℬ]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- Lemma 13.10.6 (1) (`014X`): `F` induces a shift-commuting exact functor
`HomotopyCategory 𝒜 (up ℤ) ⥤ HomotopyCategory ℬ (up ℤ)`. -/
@[stacks 014X "unbounded homotopy functor"]
#check F.mapHomotopyCategory (up ℤ)

@[stacks 014X "unbounded homotopy shift comparison"]
#check (inferInstance : (F.mapHomotopyCategory (up ℤ)).CommShift ℤ)

@[stacks 014X "exactness on unbounded homotopy categories"]
#check (inferInstance : (F.mapHomotopyCategory (up ℤ)).IsTriangulated)

/- Lemma 13.10.6 (2) (`014X`): `F` induces a shift-commuting exact functor
`HomotopyCategory.Plus 𝒜 ⥤ HomotopyCategory.Plus ℬ`. -/
@[stacks 014X "bounded-below homotopy functor"]
#check F.mapHomotopyCategoryPlus

@[stacks 014X "bounded-below homotopy shift comparison"]
#check (inferInstance : F.mapHomotopyCategoryPlus.CommShift ℤ)

@[stacks 014X "exactness on bounded-below homotopy categories"]
#check (inferInstance : F.mapHomotopyCategoryPlus.IsTriangulated)

/- Lemma 13.10.6 (3) (`014X`): `F` induces a shift-commuting exact functor
`HomotopyCategory.Minus 𝒜 ⥤ HomotopyCategory.Minus ℬ`. -/
@[stacks 014X "bounded-above homotopy functor"]
#check F.mapHomotopyCategoryMinus

@[stacks 014X "bounded-above homotopy shift comparison"]
#check (inferInstance : F.mapHomotopyCategoryMinus.CommShift ℤ)

@[stacks 014X "exactness on bounded-above homotopy categories"]
#check (inferInstance : F.mapHomotopyCategoryMinus.IsTriangulated)

/- Lemma 13.10.6 (4) (`014X`): `F` induces a shift-commuting exact functor
`HomotopyCategory.Bounded 𝒜 ⥤ HomotopyCategory.Bounded ℬ`. -/
@[stacks 014X "bounded homotopy functor"]
#check F.mapHomotopyCategoryBounded

@[stacks 014X "bounded homotopy shift comparison"]
#check (inferInstance : F.mapHomotopyCategoryBounded.CommShift ℤ)

@[stacks 014X "exactness on bounded homotopy categories"]
#check (inferInstance : F.mapHomotopyCategoryBounded.IsTriangulated)

end

end CategoryTheory
