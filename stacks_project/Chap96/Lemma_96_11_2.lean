module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable [∀ x : X.total, HasWeakSheafify
    ((inheritedFppfTopology X).over x) AddCommGrpCat.{u}]
variable [∀ x : X.total,
    ((inheritedFppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ y : Y.total, HasWeakSheafify
    ((inheritedFppfTopology Y).over y) AddCommGrpCat.{u}]
variable [∀ y : Y.total,
    ((inheritedFppfTopology Y).over y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Lemma 96.11.2: let `f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf`. The pullback functor `f^* = f⁻¹ : Mod(𝒪_Y) ⟶ Mod(𝒪_X)`
preserves quasi-coherent sheaves. -/
@[stacks 06WH]
instance pullback_isQuasicoherent
    (F : SheafOfModules.{u} (structureSheaf Y))
    [F.IsQuasicoherent] :
    ((modulePullback f).obj F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
