module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 96.11.2: let `f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf`. The pullback functor `f^* = f⁻¹ : Mod(𝒪_Y) ⟶ Mod(𝒪_X)`
preserves quasi-coherent sheaves. -/
@[stacks 06WH] #check (AlgebraicGeometry.GroupoidsOver.pullback_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [∀ x : X.total, HasWeakSheafify
      ((fppfTopology X).over x) AddCommGrpCat.{u}]
    [∀ x : X.total,
      ((fppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ y : Y.total, HasWeakSheafify
      ((fppfTopology Y).over y) AddCommGrpCat.{u}]
    [∀ y : Y.total,
      ((fppfTopology Y).over y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} (structureSheaf Y)) [F.IsQuasicoherent],
    ((modulePullback f).obj F).IsQuasicoherent)

end AlgebraicGeometry.GroupoidsOver
