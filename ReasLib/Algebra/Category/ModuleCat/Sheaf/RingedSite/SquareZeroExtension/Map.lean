module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Infinitesimal

/-!
# Maps of descended square-zero ideals

A morphism between square-zero presentations of the same ring sheaf induces a linear map
between their descended kernel modules.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite.FirstOrderThickening

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.KernelIdeal.IsSquareZero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
variable {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π1] [Sheaf.IsLocallySurjective π2]

/-- The image of the second kernel under a morphism of presentations lies in the first kernel. -/
theorem mapToTarget_kernel (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2) :
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map (KernelIdeal.ι π2) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap h)) ≫
      (SheafOfModules.toSheaf (ringSheaf J 𝒪1)).map (KernelIdeal.map π1) = 0 := sorry

/-- The additive map between descended kernel modules induced by a morphism of presentations. -/
noncomputable def mapToTarget_toSheaf (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj (idealModule hπ2) ⟶
      (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj (idealModule hπ1) :=
  (hπ2.targetModuleForgetIso inferInstance).hom ≫
    KernelIdeal.additiveLift π1
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map (KernelIdeal.ι π2) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap h))
      (mapToTarget_kernel h h_comm) ≫
    (hπ1.targetModuleForgetIso inferInstance).inv

/-- The induced additive map of descended kernels is linear over their common target ring. -/
theorem mapToTarget_smul (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2)
    (U : Cᵒᵖ) (r : (ringSheaf J 𝒪).obj.obj U) (m : (idealModule hπ2).val.obj U) :
    (mapToTarget_toSheaf h h_comm hπ1 hπ2).hom.app U (r • m) =
      ((idealModule hπ1).val.obj U).isModule.smul r
        ((mapToTarget_toSheaf h h_comm hπ1 hπ2).hom.app U m) := sorry

/-- The linear map of descended square-zero ideals induced by a morphism of presentations. -/
noncomputable def mapToTarget (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    idealModule hπ2 ⟶ idealModule hπ1 where
  val := PresheafOfModules.homMk (mapToTarget_toSheaf h h_comm hπ1 hπ2).hom
    (mapToTarget_smul h h_comm hπ1 hπ2)

/-- The induced map of descended ideals commutes with their inclusions into the source rings. -/
theorem mapToTarget_comp_ι (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    (hπ2.targetModuleForgetIso inferInstance).inv ≫
        (SheafOfModules.toSheaf (ringSheaf J 𝒪)).map (mapToTarget h h_comm hπ1 hπ2) ≫
          (hπ1.targetModuleForgetIso inferInstance).hom ≫
            (SheafOfModules.toSheaf (ringSheaf J 𝒪1)).map (KernelIdeal.ι π1) =
      (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map (KernelIdeal.ι π2) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap h) := sorry

end SheafOfModules.RingedSite.KernelIdeal.IsSquareZero
