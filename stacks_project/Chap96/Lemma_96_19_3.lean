/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Extended
import StacksCheckRecall

/-!
# Homotopy vanishing of the extended relative Čech complex of a split morphism
-/

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}
variable (f : U ⟶ X) (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
  (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/- Lemma 96.19.3: if a 1-morphism `f : U ⟶ X` of categories fibred in groupoids
over `(Sch/S)_fppf` admits a 1-morphism `s : X ⟶ U` such that `s ≫ f` is
2-isomorphic to `𝟙 X`, then the extended relative Čech complex of an abelian
presheaf `F` on `X` is homotopic to zero. Lean degree 0 is the source term `F`
in degree -1, and positive Lean degrees recover `RelativeCech.complex`. -/
@[stacks 06XA] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.extended_contractible_of_section
    f s t F : (RelativeCech.extended f F).Contractible)
