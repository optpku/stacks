/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.InverseImage
public import ReasLib.Topology.Sheaves.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition

/-! # Pullback of square-zero relative algebra extensions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open SheafOfModules.RingedSite
open TopologicalSpace Opposite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Solution

variable {S X Y : RingedSpace.{u}} {f : X ⟶ S}
variable {F : X.Modules} {G : Y.Modules}
variable (g : Y ⟶ X)

/-- The fibre-product sheaf of rings `i⁻¹ 𝒪_{Y'} ×_{𝒪_Y} g⁻¹ 𝒪_X`. -/
def pullbackAlongSheaf (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  Limits.pullback (inverseImageStructureSheafHomComm SY.i)
    (inverseImageStructureSheafHomComm g)

/-- The ringed space with underlying space Y and structure sheaf 𝒪'_2. -/
def pullbackAlongSpace (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    RingedSpace.{u} :=
  (pullbackAlongSheaf g SY).toRingedSpace

/-- The structure-sheaf projection `𝒪'_2 ⟶ g⁻¹ 𝒪_X`. -/
def pullbackAlongISharp (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlongSheaf g SY ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  Limits.pullback.snd (inverseImageStructureSheafHomComm SY.i)
    (inverseImageStructureSheafHomComm g)

/-- The first-order thickening `(Y, g⁻¹ 𝒪_X) ⟶ (Y, 𝒪'_2)`. -/
def pullbackAlongI (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    inverseImageSpace g ⟶ pullbackAlongSpace g SY :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (pullbackAlongISharp g SY).hom }

/-- The thickening `pullbackAlongI` is first-order. -/
private theorem pullbackAlong_i_isFirstOrder
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    IsFirstOrderThickening (pullbackAlongI g SY) := sorry

/-- The structure-sheaf projection `𝒪'_2 ⟶ i⁻¹ 𝒪_{Y'}`. -/
def pullbackAlongFst (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlongSheaf g SY ⟶ inverseImageX' SY :=
  Limits.pullback.fst (inverseImageStructureSheafHomComm SY.i)
    (inverseImageStructureSheafHomComm g)

/-- The two structure maps into the fibre product have equal reductions. -/
private theorem pullbackAlongSSharp_condition (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    structureMap SY ≫ inverseImageStructureSheafHomComm SY.i =
      ((Hom.StructureSheaf.compIso g f).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
          (inverseImageStructureSheafHomComm f)) ≫ inverseImageStructureSheafHomComm g := sorry

/-- The structure map `(g ≫ f)⁻¹ 𝒪_S ⟶ 𝒪'_2` induced by the two maps to
`i⁻¹ 𝒪_{Y'}` and `g⁻¹ 𝒪_X`. -/
@[no_expose] def pullbackAlongSSharp (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (g ≫ f).hom.base).obj S.sheaf ⟶
      pullbackAlongSheaf g SY :=
  Limits.pullback.lift (structureMap SY)
    ((Hom.StructureSheaf.compIso g f).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
        (inverseImageStructureSheafHomComm f))
    (pullbackAlongSSharp_condition g SY)

/-- The morphism of ringed spaces `(Y, 𝒪'_2) ⟶ S`. -/
def pullbackAlongF' (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlongSpace g SY ⟶ S :=
  InducedCategory.homMk
    { base := (g ≫ f).hom.base
      c :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (g ≫ f).hom.base).homEquiv S.sheaf (pullbackAlongSheaf g SY)
          (pullbackAlongSSharp g SY)).hom }

/-- The first component of a kernel section reduces to zero. -/
private theorem pullbackAlongKernelToPushforward_mem (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (x : (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.obj U) :
    (pullbackAlongFst g SY).hom.app U
      (KernelIdeal.ιApp (commRingSheafPushforwardMap (pullbackAlongI g SY)) U x) ∈ KernelIdeal.sectionIdeal (inverseImageStructureSheafHomComm SY.i) U := sorry

/-- The first component of a fibre-product kernel section, identified with the coefficient. -/
@[expose] private def pullbackAlongKernelToPushforwardApp (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (x : (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.obj U) :
    G.val.obj U :=
  (SY.kernelIso.hom).val.app U
                  ((@targetModuleToIdealModule _ _ SY.i SY.i_isFirstOrder).val.app U
                    (((@inverseImage_isSquareZero _ _ SY.i SY.i_isFirstOrder).targetModuleForgetIso
                          (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
            (inverseImageStructureSheafHomComm SY.i) inferInstance
            (@instInverseImage_isLocallySurjective _ _ SY.i SY.i_isFirstOrder.toIsThickening))).inv.hom.app U
                      ((KernelIdeal.sectionsIso
                            (inverseImageStructureSheafHomComm SY.i) U).inv
                        ⟨(pullbackAlongFst g SY).hom.app U
                            (KernelIdeal.ιApp
                              (commRingSheafPushforwardMap (pullbackAlongI g SY)) U x),
                          pullbackAlongKernelToPushforward_mem g SY U x⟩)))

/-- The section map preserves addition. -/
private theorem pullbackAlongKernelToPushforward_map_add (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (x y : (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.obj U) :
    pullbackAlongKernelToPushforwardApp g SY U (x + y) = pullbackAlongKernelToPushforwardApp g SY U x + pullbackAlongKernelToPushforwardApp g SY U y := sorry

/-- The additive section maps commute with restrictions. -/
private theorem pullbackAlongKernelToPushforward_naturality (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    {U V : (Opens Y)ᵒᵖ} (ρ : U ⟶ V) :
    (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.presheaf.map ρ ≫
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pullbackAlongKernelToPushforwardApp g SY V)
        (pullbackAlongKernelToPushforward_map_add g SY V)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pullbackAlongKernelToPushforwardApp g SY U)
        (pullbackAlongKernelToPushforward_map_add g SY U)) ≫
        (((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G)).val.presheaf.map ρ := sorry

/-- The section map respects the structure-sheaf scalar action. -/
private theorem pullbackAlongKernelToPushforward_map_smul (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (r : (pullbackAlongSpace g SY).ringCatSheaf.obj.obj U)
    (x : (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.obj U) :
    pullbackAlongKernelToPushforwardApp g SY U (r • x) = (ModuleCat.smul
      ((((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G)).val.obj U) r).hom
        (pullbackAlongKernelToPushforwardApp g SY U x) := sorry

/-- The `𝒪'_2`-module map `Ker((pullbackAlongI)^♯) ⟶ (pullbackAlongI)_* G` reading the
first fibre-product component through `SY.kernelIso`. -/
@[no_expose] def pullbackAlongKernelToPushforward
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Hom.kernelIdealSheaf (pullbackAlongI g SY) ⟶
      ((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G) := by
  exact {
    val := PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
          (pullbackAlongKernelToPushforwardApp g SY U)
          (pullbackAlongKernelToPushforward_map_add g SY U))
        naturality {_ _} ρ := pullbackAlongKernelToPushforward_naturality g SY ρ }
      (pullbackAlongKernelToPushforward_map_smul g SY) }

/-- Inclusion of a coefficient of `G` into `i⁻¹ 𝒪_{Y'}`. -/
@[expose] private def pullbackAlongKernelιApp
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (inverseImageX' SY).obj.obj U :=
  KernelIdeal.ιApp (inverseImageStructureSheafHomComm SY.i) U
    (((@inverseImage_isSquareZero _ _ SY.i SY.i_isFirstOrder).targetModuleForgetIso
          (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
            (inverseImageStructureSheafHomComm SY.i) inferInstance
            (@instInverseImage_isLocallySurjective _ _ SY.i SY.i_isFirstOrder.toIsThickening))).hom.hom.app U
      ((@idealModuleToTargetModule _ _ SY.i SY.i_isFirstOrder).val.app U ((SY.kernelIso.inv).val.app U n)))

/-- The coefficient section and zero section have the same reduction. -/
private theorem pullbackAlongPushforwardToKernel_condition (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (inverseImageStructureSheafHomComm SY.i).hom.app U
      (pullbackAlongKernelιApp g SY U n) =
      (inverseImageStructureSheafHomComm g).hom.app U 0 := sorry

/-- The paired coefficient section lies in the kernel of the second projection. -/
private theorem pullbackAlongPushforwardToKernel_mem (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    TopCat.Sheaf.CommRing.pullbackSectionMk (inverseImageStructureSheafHomComm SY.i)
      (inverseImageStructureSheafHomComm g) U (pullbackAlongKernelιApp g SY U n) 0
      (pullbackAlongPushforwardToKernel_condition g SY U n) ∈
      KernelIdeal.sectionIdeal (commRingSheafPushforwardMap (pullbackAlongI g SY)) U := sorry

/-- The coefficient section inserted into the kernel by the pair `(ι n, 0)`. -/
@[expose] private def pullbackAlongPushforwardToKernelApp (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.obj U :=
  (KernelIdeal.sectionsIso
      (commRingSheafPushforwardMap (pullbackAlongI g SY)) U).inv
    ⟨TopCat.Sheaf.CommRing.pullbackSectionMk (inverseImageStructureSheafHomComm SY.i)
      (inverseImageStructureSheafHomComm g) U (pullbackAlongKernelιApp g SY U n) 0
      (pullbackAlongPushforwardToKernel_condition g SY U n), pullbackAlongPushforwardToKernel_mem g SY U n⟩

/-- The section map preserves addition. -/
private theorem pullbackAlongPushforwardToKernel_map_add (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (x y : (((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G)).val.obj U) :
    pullbackAlongPushforwardToKernelApp g SY U (x + y) = pullbackAlongPushforwardToKernelApp g SY U x + pullbackAlongPushforwardToKernelApp g SY U y := sorry

/-- The additive section maps commute with restrictions. -/
private theorem pullbackAlongPushforwardToKernel_naturality (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    {U V : (Opens Y)ᵒᵖ} (ρ : U ⟶ V) :
    (((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G)).val.presheaf.map ρ ≫
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pullbackAlongPushforwardToKernelApp g SY V)
        (pullbackAlongPushforwardToKernel_map_add g SY V)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pullbackAlongPushforwardToKernelApp g SY U)
        (pullbackAlongPushforwardToKernel_map_add g SY U)) ≫
        (Hom.kernelIdealSheaf (pullbackAlongI g SY)).val.presheaf.map ρ := sorry

/-- The section map respects the structure-sheaf scalar action. -/
private theorem pullbackAlongPushforwardToKernel_map_smul (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (r : (pullbackAlongSpace g SY).ringCatSheaf.obj.obj U)
    (x : (((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G)).val.obj U) :
    pullbackAlongPushforwardToKernelApp g SY U (r • x) = r • pullbackAlongPushforwardToKernelApp g SY U x := sorry

/-- The `𝒪'_2`-module map `(pullbackAlongI)_* G ⟶ Ker((pullbackAlongI)^♯)` sending `n`
to the class of `(ι n, 0)`. -/
@[no_expose] def pullbackAlongPushforwardToKernel
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    ((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G) ⟶
      Hom.kernelIdealSheaf (pullbackAlongI g SY) := by
  exact {
    val := PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
          (pullbackAlongPushforwardToKernelApp g SY U)
          (pullbackAlongPushforwardToKernel_map_add g SY U))
        naturality {_ _} ρ := pullbackAlongPushforwardToKernel_naturality g SY ρ }
      (pullbackAlongPushforwardToKernel_map_smul g SY) }

/-- The kernel comparison followed by coefficient insertion is the identity. -/
private theorem pullbackAlongKernelIso_hom_inv_id (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (((pullbackAlongI g SY)^*).map (pullbackAlongKernelToPushforward g SY) ≫
      (pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
        (restrictToInverseImage g G)) ≫ ((@asIso _ _ _ _
        ((pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
          (restrictToInverseImage g G))
        (@instIsIso_counit_app _ _ _ (pullbackAlong_i_isFirstOrder g SY).toIsThickening _)).inv ≫
      ((pullbackAlongI g SY)^*).map (pullbackAlongPushforwardToKernel g SY)) = 𝟙 _ := sorry

/-- Coefficient insertion followed by the kernel comparison is the identity. -/
private theorem pullbackAlongKernelIso_inv_hom_id (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    ((@asIso _ _ _ _
        ((pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
          (restrictToInverseImage g G))
        (@instIsIso_counit_app _ _ _ (pullbackAlong_i_isFirstOrder g SY).toIsThickening _)).inv ≫
      ((pullbackAlongI g SY)^*).map (pullbackAlongPushforwardToKernel g SY)) ≫ (((pullbackAlongI g SY)^*).map (pullbackAlongKernelToPushforward g SY) ≫
      (pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
        (restrictToInverseImage g G)) = 𝟙 _ := sorry

/-- Identification of the pullback kernel with its restricted coefficient module. -/
@[no_expose] def pullbackAlongKernelIso
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Hom.idealModule (pullbackAlongI g SY) ≅ restrictToInverseImage g G where
  hom :=
    ((pullbackAlongI g SY)^*).map (pullbackAlongKernelToPushforward g SY) ≫
      (pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
        (restrictToInverseImage g G)
  inv :=
    (@asIso _ _ _ _
        ((pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
          (restrictToInverseImage g G))
        (@instIsIso_counit_app _ _ _ (pullbackAlong_i_isFirstOrder g SY).toIsThickening _)).inv ≫
      ((pullbackAlongI g SY)^*).map (pullbackAlongPushforwardToKernel g SY)
  hom_inv_id := pullbackAlongKernelIso_hom_inv_id g SY
  inv_hom_id := pullbackAlongKernelIso_inv_hom_id g SY

/-- The pullback thickening and ambient map commute over the base. -/
private theorem pullbackAlong_commutes (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlongI g SY ≫ pullbackAlongF' g SY = (inverseImageTo g ≫ f) ≫ 𝟙 S := sorry

/-- The pullback kernel map is the zero identity-base coefficient map. -/
private theorem pullbackAlong_induces (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    kernelMapOf (𝟙 S) (inverseImageTo g ≫ f) (pullbackAlongI g SY)
      (pullbackAlong_i_isFirstOrder g SY) (pullbackAlongF' g SY) (pullbackAlong_commutes g SY) ≫
      ((inverseImageTo g ≫ f) _*).map (pullbackAlongKernelIso g SY).hom =
        zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G) := sorry

/-- Pullback of 0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 along g^♯, as a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension of g⁻¹ 𝒪_X by G. -/
def pullbackAlong (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Solution (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
      (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G)) :=
  @Solution.of _ _ _ (𝟙 S) inferInstance (inverseImageTo g ≫ f) (restrictToInverseImage g G)
    (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G))
    _ (pullbackAlongI g SY) (by exact pullbackAlong_i_isFirstOrder g SY)
    (pullbackAlongF' g SY) (by exact pullbackAlong_commutes g SY)
    (pullbackAlongKernelIso g SY) (by exact pullbackAlong_induces g SY)

/-- The projection 𝒪'_2 ⟶ g⁻¹ 𝒪_X is the second projection of the sheaf
fibre product. -/
theorem pullbackAlong_spec (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (pullbackAlong g SY).i = pullbackAlongI g SY ∧
      (pullbackAlong g SY).f' = pullbackAlongF' g SY ∧
        (pullbackAlong g SY).kernelIso = pullbackAlongKernelIso g SY := ⟨rfl, rfl, rfl⟩

/-- The morphism of ringed spaces `(Y, i⁻¹ 𝒪_{Y'}) ⟶ (Y, 𝒪'_2)` with identity
underlying map and structure map `𝒪'_2 ⟶ i⁻¹ 𝒪_{Y'}`. -/
def fromPullbackAlongHom
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    inverseImageSpace SY.i ⟶ pullbackAlongSpace g SY :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (pullbackAlongFst g SY).hom }

/-- The first projection of the fibre product gives a commuting top face. -/
theorem fromPullbackAlong_comm_top (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    fromInverseImage SY.i ≫ fromPullbackAlongHom g SY =
      fromInverseImage g ≫ (pullbackAlong g SY).i := sorry

/-- The first projection of the fibre product respects the ambient map. -/
theorem fromPullbackAlong_comm_right (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    fromPullbackAlongHom g SY ≫ (pullbackAlong g SY).f' =
      (inverseImageTo SY.i ≫ SY.f') ≫ 𝟙 S := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Solution
