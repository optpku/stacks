module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SheafificationMonoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal comparisons for sheafification over a ringed site

This leaf records the reusable tensor comparison API available once a monoidal
structure on fixed-ring module sheafification is supplied by the caller.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

namespace ModuleSheafification

/-- The tensor comparison from the tensor product of two sheafified module presheaves to the
sheafification of their tensor product over a fixed ring sheaf. -/
@[stacks 05NA "tensor comparison for module sheafification"]
noncomputable abbrev tensorIso
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    CategoryTheory.MonoidalCategory.tensorObj
        ((moduleSheafification 𝒪).obj ℱ)
        ((moduleSheafification 𝒪).obj 𝒢) ≅
      ModuleSheafification.tensorObj 𝒪 ℱ 𝒢 :=
  PresheafOfModules.sheafificationTensorIso (𝟙 (ringSheaf J 𝒪).obj) ℱ 𝒢

/-- The oplax tensor comparison from sheafification of a tensor product to the tensor product of
the two fixed-ring sheafifications. -/
@[stacks 05NA "oplax tensor comparison for module sheafification"]
noncomputable abbrev tensorComparison
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    (moduleSheafification 𝒪).obj
        (CategoryTheory.MonoidalCategory.tensorObj ℱ 𝒢) ⟶
      CategoryTheory.MonoidalCategory.tensorObj
        ((moduleSheafification 𝒪).obj ℱ)
        ((moduleSheafification 𝒪).obj 𝒢) :=
  PresheafOfModules.sheafificationTensorComparison (𝟙 (ringSheaf J 𝒪).obj) ℱ 𝒢

/-- Fixed-ring module sheafification commutes with right tensoring through its supplied monoidal
comparison. -/
@[stacks 05NA "module sheafification and right tensoring"]
noncomputable abbrev tensorRightIso
    (ℱ : PresheafOfModules (ringSheaf J 𝒪).obj) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification 𝒪 ≅
      moduleSheafification 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ) :=
  PresheafOfModules.sheafificationTensorRightIso (𝟙 (ringSheaf J 𝒪).obj) ℱ

/-- Fixed-ring module sheafification commutes with left tensoring through its supplied monoidal
comparison. -/
@[stacks 05NA "module sheafification and left tensoring"]
noncomputable abbrev tensorLeftIso
    (ℱ : PresheafOfModules (ringSheaf J 𝒪).obj) :
    CategoryTheory.MonoidalCategory.tensorLeft ℱ ⋙ moduleSheafification 𝒪 ≅
      moduleSheafification 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorLeft ((moduleSheafification 𝒪).obj ℱ) :=
  PresheafOfModules.sheafificationTensorLeftIso (𝟙 (ringSheaf J 𝒪).obj) ℱ

/-- The tensor product of two module sheaves is canonically identified with the sheafification
of the tensor product of their underlying module presheaves. -/
@[stacks 03L6 "module-sheaf tensor as a sheafified pointwise tensor"]
noncomputable def tensorObjIso
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) :
    moduleTensor ℱ 𝒢 ≅
      ModuleSheafification.tensorObj 𝒪 ℱ.val 𝒢.val :=
  (CategoryTheory.MonoidalCategory.tensorIso
      (moduleSheafificationValIso 𝒪 ℱ).symm
      (moduleSheafificationValIso 𝒪 𝒢).symm :
    moduleTensor ℱ 𝒢 ≅
      CategoryTheory.MonoidalCategory.tensorObj
        ((moduleSheafification 𝒪).obj ℱ.val)
        ((moduleSheafification 𝒪).obj 𝒢.val)) ≪≫
    tensorIso 𝒪 ℱ.val 𝒢.val



end ModuleSheafification

end SheafOfModules.RingedSite
