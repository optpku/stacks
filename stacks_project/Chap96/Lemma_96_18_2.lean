/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_18_2_Extended
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy vanishing of the extended Čech complex of a split covering
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Lemma 96.18.2: if a 1-morphism `f : U ⟶ X` of categories fibred in groupoids
over `(Sch/S)_fppf` admits a 1-morphism `s : X ⟶ U` such that `s ≫ f` is
2-isomorphic to `𝟙 X`, then the extended Čech complex of an abelian presheaf
`F` on `X` is homotopic to zero. Lean degree 0 is the source term `Γ(X, F)` in
degree -1, and positive Lean degrees recover `Cech.complex`. -/
@[stacks 06X6]
theorem cechExtended_contractible (f : U ⟶ X) (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Cech.extended f F).Contractible :=
  sorry
