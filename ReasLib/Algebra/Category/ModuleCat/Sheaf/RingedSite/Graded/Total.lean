module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.NatMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.GradedObject.Monoid
public import ReasLib.CategoryTheory.GradedObject.Total.Monoidal

/-!
# Total algebras of graded algebra sheaves

This file constructs the commutative algebra sheaf obtained by taking the coproduct of the
homogeneous pieces of an ordinarily commutative naturally graded algebra sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The total commutative algebra of an ordinarily commutative naturally graded algebra sheaf. -/
noncomputable def totalAlgebra
    (A : GradedAlgebraSheaf O ℕ) [A.IsCommutative] : Under O := by
  let s : (A 0).val.sections :=
    PresheafOfModules.sectionsMk (fun U => A.one U) (fun {_ _} f => A.map_one f)
  let one0 : unitModule J O ⟶ A 0 := (A 0).unitHomEquiv.symm s
  let one : 𝟙_ (ringedSiteModuleCategory J O) ⟶ A 0 :=
    (unitIsoTensorUnit (J := J) (𝒪 := O)).inv ≫ one0
  let mon : MonObj A.toGradedObject :=
    GradedObject.Monoidal.monObj A.toGradedObject one (mulHom A)
      (by sorry) (by sorry) (by sorry)
  let comm : @IsCommMonObj _ _ _ _ A.toGradedObject mon := by
    refine { mul_comm := ?_ }
    sorry
  let graded : CommMon (GradedObject ℕ (ringedSiteModuleCategory J O)) :=
    @CommMon.mk _ _ _ _ A.toGradedObject mon comm
  let total : CommMon (ringedSiteModuleCategory J O) :=
    (GradedObject.Total.functor
      (I := ℕ) (C := ringedSiteModuleCategory J O)).mapCommMon.obj graded
  let mulSection (U : Cᵒᵖ) (x y : total.X.val.obj U) : total.X.val.obj U :=
    ((μ[total.X]).val.app U).hom (tensorSection O U x y)
  let oneSection (U : Cᵒᵖ) : total.X.val.obj U :=
    ((η[total.X]).val.app U).hom
      (((unitIsoTensorUnit (J := J) (𝒪 := O)).hom.val.app U).hom (1 : O.obj.obj U))
  let sectionRing (U : Cᵒᵖ) : CommRing (total.X.val.obj U) :=
    { (inferInstance : AddCommGroup (total.X.val.obj U)) with
      mul := mulSection U
      one := oneSection U
      mul_assoc := by sorry
      one_mul := by sorry
      mul_one := by sorry
      zero_mul := by sorry
      mul_zero := by sorry
      left_distrib := by sorry
      right_distrib := by sorry
      mul_comm := by sorry }
  let obj (U : Cᵒᵖ) : CommRingCat.{max u v} :=
    @CommRingCat.of (total.X.val.obj U) (sectionRing U)
  let map {U V : Cᵒᵖ} (f : U ⟶ V) : obj U ⟶ obj V :=
    CommRingCat.ofHom
      { toFun := fun x => (total.X.val.map f).hom x
        map_zero' := by sorry
        map_one' := by sorry
        map_add' := by sorry
        map_mul' := by sorry }
  let presheaf : Cᵒᵖ ⥤ CommRingCat.{max u v} :=
    { obj := obj
      map := fun f => map f
      map_id := by sorry
      map_comp := by sorry }
  let algebraSheaf : Sheaf J CommRingCat.{max u v} :=
    ⟨presheaf, by sorry⟩
  let structureMap : O ⟶ algebraSheaf :=
    ObjectProperty.homMk
      { app := fun U => CommRingCat.ofHom
          { toFun := fun r => r • oneSection U
            map_zero' := by sorry
            map_one' := by sorry
            map_add' := by sorry
            map_mul' := by sorry }
        naturality := by sorry }
  exact Under.mk structureMap

/-- The module underlying the total algebra is the coproduct of its homogeneous pieces. -/
noncomputable def totalUnderlyingModuleIso
    (A : GradedAlgebraSheaf O ℕ) [A.IsCommutative] :
    (GradedObject.Total.functor
        (I := ℕ) (C := ringedSiteModuleCategory J O)).obj A.toGradedObject ≅
      (restrictionAlong (totalAlgebra O A).hom).obj
        (unitModule J (totalAlgebra O A).right) where
  hom :=
    { val :=
        { app := fun U =>
            let X := ((GradedObject.Total.functor
              (I := ℕ) (C := ringedSiteModuleCategory J O)).obj A.toGradedObject).val.obj U
            let Y := ((restrictionAlong (totalAlgebra O A).hom).obj
              (unitModule J (totalAlgebra O A).right)).val.obj U
            @ModuleCat.ofHom _ _ X Y inferInstance inferInstance inferInstance inferInstance
            { toFun := fun x : X => (x : Y)
              map_add' := by sorry
              map_smul' := by sorry }
          naturality := by sorry } }
  inv :=
    { val :=
        { app := fun U =>
            let X := ((restrictionAlong (totalAlgebra O A).hom).obj
              (unitModule J (totalAlgebra O A).right)).val.obj U
            let Y := ((GradedObject.Total.functor
              (I := ℕ) (C := ringedSiteModuleCategory J O)).obj A.toGradedObject).val.obj U
            @ModuleCat.ofHom _ _ X Y inferInstance inferInstance inferInstance inferInstance
            { toFun := fun x : X => (x : Y)
              map_add' := by sorry
              map_smul' := by sorry }
          naturality := by sorry } }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- The comparison with the underlying module carries each homogeneous inclusion to the same
sectionwise inclusion. -/
theorem totalUnderlyingModuleIso_hom_ι
    (A : GradedAlgebraSheaf O ℕ) [A.IsCommutative] (n : ℕ) (U : Cᵒᵖ)
    (x : (A n).val.obj U) :
    (((Sigma.ι A.toGradedObject n ≫ (totalUnderlyingModuleIso O A).hom).val.app U).hom x) =
      ((Sigma.ι A.toGradedObject n).val.app U).hom x := sorry

end SheafOfModules.RingedSite.GradedAlgebraSheaf
