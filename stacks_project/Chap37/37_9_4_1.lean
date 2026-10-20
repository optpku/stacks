/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {S X X' Y Y' : AlgebraicGeometry.Scheme.{u}}
variable (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
variable [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
variable [AlgebraicGeometry.IsFirstOrderThickening i]
variable [AlgebraicGeometry.IsFirstOrderThickening j]
variable [i.IsOver S] [j.IsOver S] [a.IsOver S]
variable (A : (AlgebraicGeometry.Scheme.Modules.pullback a).obj
  (AlgebraicGeometry.Scheme.Hom.conormalSheaf j) ⟶
    AlgebraicGeometry.Scheme.Hom.conormalSheaf i)

/- 37.9.4.1: to `U' : X'.Opens`, assign the set of morphisms `a' : U'.toScheme ⟶ Y'`
over `S` which restrict to `a` on `i ⁻¹ᵁ U'` and induce the prescribed restriction of the
conormal map `A`. -/
@[stacks 04FI] #check (AlgebraicGeometry.Scheme.Hom.Deformation.sections S i j a A :
  (U' : X'.Opens) → Set (U'.toScheme ⟶ Y'))
