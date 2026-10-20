/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRingSheafificationMonoidal
import StacksCheckRecall

/-!
# Lemma 18.26.1

The comparison is owned by the commutative-ring module-presheaf sheafification API; the chapter
item only recalls that reusable specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)
open PresheafOfModules

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [Functor.Monoidal (moduleSheafification J O)]

/- Lemma 18.26.1 (0GMW): sheafification carries the tensor bifunctor to the tensor bifunctor
through a canonical natural isomorphism. -/
@[stacks 0GMW]
#check
  (moduleSheafificationTensorNatIso J O :
    Functor.prod (moduleSheafification J O) (moduleSheafification J O) ⋙
        MonoidalCategory.tensor
          (ringedSiteModuleCategory J (commRingSheafification J O)) ≅
      MonoidalCategory.tensor (PresheafOfModules (ringPresheaf O)) ⋙
        moduleSheafification J O)

variable (F G : PresheafOfModules (ringPresheaf O))

/- Its component is the tensor product of the two sheafifications identified with the
sheafification of the presheaf tensor product. -/
#check
  (moduleSheafificationTensorIso J O F G :
    MonoidalCategory.tensorObj
        ((moduleSheafification J O).obj F)
        ((moduleSheafification J O).obj G) ≅
      (moduleSheafification J O).obj (Monoidal.tensorObj F G))

/- The comparison in the source direction is the inverse morphism of the canonical tensor
isomorphism. -/
#check
  (moduleSheafificationTensorComparison J O F G :
    (moduleSheafification J O).obj (Monoidal.tensorObj F G) ⟶
      MonoidalCategory.tensorObj
        ((moduleSheafification J O).obj F)
        ((moduleSheafification J O).obj G))

end PresheafOfModules
