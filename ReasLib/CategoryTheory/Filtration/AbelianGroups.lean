module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Field.Defs
public import ReasLib.Algebra.Category.FGTorsionFreeModuleCat.Basic
public import ReasLib.CategoryTheory.Filtration.Preabelian
public import ReasLib.CategoryTheory.Filtration.Preadditive

@[expose] public section

universe u v w

namespace CategoryTheory.FilteredObject

/-- The category of filtered abelian groups is equivalent neither to filtered vector spaces
over any field nor to finitely generated torsion-free modules over any Noetherian domain. -/
theorem addCommGrp_not_equivalent_module_categories :
    (∀ (k : Type w) [Field k],
      ¬ Nonempty (FilteredObject AddCommGrpCat.{u} ≌ FilteredObject (ModuleCat.{v} k))) ∧
    (∀ (R : Type w) [CommRing R] [IsDomain R] [IsNoetherianRing R],
      ¬ Nonempty (FilteredObject AddCommGrpCat.{u} ≌ FGTorsionFreeModuleCat.{v} R)) := sorry

end CategoryTheory.FilteredObject
