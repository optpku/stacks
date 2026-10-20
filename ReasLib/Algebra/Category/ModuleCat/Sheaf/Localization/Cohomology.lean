module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Injective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology on localized ringed sites

Cohomology over an object of a ringed site agrees with cohomology at the terminal object of the
corresponding slice site.  The comparison is exposed first on the module-valued derived functor,
then on underlying additive sheaves, and finally as a global-cohomology statement.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace SheafOfModules.Localization.Cohomology

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (R : Sheaf J RingCat.{max u v}) (U : C)
variable [(restriction R U : SheafOfModules.{max u v} R ⥤
  SheafOfModules.{max u v} (R.over U)).IsRightAdjoint]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]
variable [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf (J.over U) AddCommGrpCat.{max u v})]

/-- Module-valued cohomology at `U` agrees with cohomology at the terminal object of the slice
site over `U`. -/
@[stacks 03F3 "module-valued cohomology on a localized site"]
theorem atObject_isomorphic
    (F : SheafOfModules.{max u v} R) (p : ℕ) :
    IsIsomorphic
      ((SheafOfModules.cohomologyAtObjectFunctor R p U).obj F)
      ((SheafOfModules.cohomologyAtObjectFunctor (R.over U) p
        (Over.mk (𝟙 U))).obj ((restriction R U).obj F)) := sorry

/-- Cohomology of the underlying additive sheaf at `U` agrees with cohomology of its localized
restriction at the terminal slice object. -/
@[stacks 03F3 "underlying cohomology at the terminal slice object"]
theorem atTerminal_isomorphic
    (F : SheafOfModules.{max u v} R) (p : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf R).obj F).H' p U)
      (((SheafOfModules.toSheaf (R.over U)).obj
        ((restriction R U).obj F)).H' p (Over.mk (𝟙 U))) := sorry

/-- Cohomology of a module sheaf over `U` agrees with global cohomology of its restriction to the
slice site over `U`. -/
@[stacks 03F3 "cohomology over an object as localized global cohomology"]
theorem global_isomorphic
    (F : SheafOfModules.{max u v} R) (p : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf R).obj F).H' p U)
      (AddCommGrpCat.of
        (((SheafOfModules.toSheaf (R.over U)).obj
          ((restriction R U).obj F)).H p)) := sorry

end SheafOfModules.Localization.Cohomology
