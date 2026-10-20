module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal comparisons for commutative-ring module-presheaf sheafification

This leaf specializes the general module-sheafification tensor comparisons to
the canonical sheafification of a commutative-ring-valued presheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [Functor.Monoidal (moduleSheafification J 𝒪)]

/-- Lemma 18.26.1 (0GMW): module sheafification intertwines the tensor bifunctors through the
canonical monoidal natural isomorphism. -/
@[stacks 0GMW]
noncomputable abbrev moduleSheafificationTensorNatIso :
    Functor.prod (moduleSheafification J 𝒪) (moduleSheafification J 𝒪) ⋙
        MonoidalCategory.tensor
          (ringedSiteModuleCategory J (commRingSheafification J 𝒪)) ≅
      MonoidalCategory.tensor (PresheafOfModules (ringPresheaf 𝒪)) ⋙
        moduleSheafification J 𝒪 :=
  Functor.Monoidal.μNatIso (moduleSheafification J 𝒪)

/-- The component of `moduleSheafificationTensorNatIso` at two module presheaves. -/
noncomputable abbrev moduleSheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules (ringPresheaf 𝒪)) :
    CategoryTheory.MonoidalCategory.tensorObj
        ((moduleSheafification J 𝒪).obj ℱ)
        ((moduleSheafification J 𝒪).obj 𝒢) ≅
      (moduleSheafification J 𝒪).obj
        (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) :=
  (moduleSheafificationTensorNatIso J 𝒪).app (ℱ, 𝒢)

/-- The canonical-specialization oplax tensor comparison from sheafification of a tensor product
to the tensor product of the two sheafifications. -/
noncomputable abbrev moduleSheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules (ringPresheaf 𝒪)) :
    (moduleSheafification J 𝒪).obj
        (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) ⟶
      CategoryTheory.MonoidalCategory.tensorObj
        ((moduleSheafification J 𝒪).obj ℱ)
        ((moduleSheafification J 𝒪).obj 𝒢) :=
  sheafificationTensorComparison (sheafificationRingMap J 𝒪) ℱ 𝒢

/-- Canonical commutative-ring module sheafification commutes with right tensoring. -/
noncomputable abbrev moduleSheafificationTensorRightIso
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification J 𝒪 ≅
      moduleSheafification J 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification J 𝒪).obj ℱ) :=
  sheafificationTensorRightIso (sheafificationRingMap J 𝒪) ℱ

/-- Canonical commutative-ring module sheafification commutes with left tensoring. -/
noncomputable abbrev moduleSheafificationTensorLeftIso
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    CategoryTheory.MonoidalCategory.tensorLeft ℱ ⋙ moduleSheafification J 𝒪 ≅
      moduleSheafification J 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorLeft ((moduleSheafification J 𝒪).obj ℱ) :=
  sheafificationTensorLeftIso (sheafificationRingMap J 𝒪) ℱ

/- Any `sorryAx` below is inherited from proof-law fields of the supplied monoidal structures;
the comparison data is the canonical generic monoidal natural isomorphism. -/

end PresheafOfModules
