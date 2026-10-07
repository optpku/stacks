module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_19_3_Extended
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy vanishing of the extended relative Čech complex of a split covering
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Lemma 96.19.3: if a 1-morphism `f : U ⟶ X` of categories fibred in groupoids
over `(Sch/S)_fppf` admits a 1-morphism `s : X ⟶ U` such that `s ≫ f` is
2-isomorphic to `𝟙 X`, then the extended relative Čech complex of an abelian
presheaf `F` on `X` is homotopic to zero. Lean degree 0 is the source term `F`
in degree -1, and positive Lean degrees recover `RelativeCech.complex`. -/
@[stacks 06XA]
theorem relativeCechExtended_contractible (f : U ⟶ X) (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (RelativeCech.extended f F).Contractible :=
  sorry
