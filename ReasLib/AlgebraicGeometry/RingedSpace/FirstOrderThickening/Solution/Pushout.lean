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
public import ReasLib.AlgebraicGeometry.RingedSpace.SquareZeroExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient

/-! # Pushout of square-zero relative algebra extensions -/

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

/-- Inverse image of `i⁻¹ 𝒪_{X'}` along `g`, as a sheaf of rings on Y. -/
def inverseImageX'Along (g : Y ⟶ X)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj (inverseImageX' SX)

/-- The map `g⁻¹ (i⁻¹ 𝒪_{X'}) ⟶ g⁻¹ 𝒪_X`. -/
def inverseImageX'AlongTo (g : Y ⟶ X)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageX'Along g SX ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
    (inverseImageStructureSheafHomComm SX.i)

/-- Inverse image of the thickening `SX.i` along `g`, as a ringed space on Y. -/
def inverseImageAlongSpace (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    RingedSpace.{u} :=
  (inverseImageX'Along g SX).toRingedSpace

/-- The first-order thickening `(Y, g⁻¹ 𝒪_X) ⟶ (Y, g⁻¹ 𝒪_{X'})`. -/
def inverseImageAlongI (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageSpace g ⟶ inverseImageAlongSpace g SX :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (inverseImageX'AlongTo g SX).hom }

/-- The thickening `inverseImageAlongI` is first-order. -/
private theorem inverseImageAlongI_isFirstOrder
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    IsFirstOrderThickening (inverseImageAlongI g SX) := sorry

/-- The morphism `(Y, g⁻¹ 𝒪_{X'}) ⟶ X'` with underlying map `g ≫ SX.i`. -/
def inverseImageAlongToX' (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongSpace g SX ⟶ SX.space :=
  InducedCategory.homMk
    { base := (g ≫ SX.i).hom.base
      c :=
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
              (g ≫ SX.i).hom.base).unit.app SX.space.sheaf) ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} (g ≫ SX.i).hom.base).map
            (Hom.StructureSheaf.compIso g SX.i).inv).hom }

/-- `inverseImageAlongI` then `inverseImageAlongToX'` recovers `inverseImageTo g ≫ SX.i`. -/
private theorem inverseImageAlongI_comp_toX' (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongI g SX ≫ inverseImageAlongToX' g SX =
      inverseImageTo g ≫ SX.i := sorry

/-- Comparison `(inverseImageTo g)^* Ker(SX.i) ⟶ Ker(inverseImageAlongI)` induced by the
morphism of thickenings `inverseImageAlongToX'`. -/
def inverseImageAlongKernelComparison
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (inverseImageTo g)^*.obj (Hom.idealModule SX.i) ⟶
      Hom.idealModule (inverseImageAlongI g SX) :=
  ((pullbackPushforwardAdjunction (inverseImageTo g)).homEquiv
      (Hom.idealModule SX.i) (Hom.idealModule (inverseImageAlongI g SX))).symm
    (@kernelMapOf _ _ _ SX.i SX.i_isFirstOrder (inverseImageTo g) _
      (inverseImageAlongI g SX) (by exact inverseImageAlongI_isFirstOrder g SX)
      (inverseImageAlongToX' g SX) (by exact inverseImageAlongI_comp_toX' g SX))

/-- `inverseImageAlongKernelComparison` is an isomorphism of kernel modules. -/
private theorem inverseImageAlongKernelComparison_isIso
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    IsIso (inverseImageAlongKernelComparison g SX) := sorry

/-- `inverseImageAlongKernelComparison` is the adjunct of `kernelMapOf` for
`inverseImageAlongToX'`. -/
theorem inverseImageAlongKernelComparison_spec
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongKernelComparison g SX =
      ((pullbackPushforwardAdjunction (inverseImageTo g)).homEquiv
          (Hom.idealModule SX.i) (Hom.idealModule (inverseImageAlongI g SX))).symm
        (@kernelMapOf _ _ _ SX.i SX.i_isFirstOrder (inverseImageTo g) _
      (inverseImageAlongI g SX) (by exact inverseImageAlongI_isFirstOrder g SX)
          (inverseImageAlongToX' g SX) (by exact inverseImageAlongI_comp_toX' g SX)) := rfl

/-- Adjunct of `c` as a map of `g⁻¹ 𝒪_X`-modules
`(inverseImageTo g)^* F ⟶ restrictToInverseImage g G`. -/
def pushoutCoeff (c : (g^*).obj F ⟶ G) :
    (inverseImageTo g)^*.obj F ⟶ restrictToInverseImage g G :=
  (pullbackPushforwardAdjunction (fromInverseImage g)).homEquiv
      ((inverseImageTo g)^*.obj F) G
    ((pullbackCompIso (fromInverseImage g) (inverseImageTo g)).inv.app F ≫
      (eqToIso
          (congrArg (fun h : Y ⟶ X ↦ Hom.pullback h) (fromInverseImage_comp g))).hom.app F ≫
        c)

/-- `pushoutCoeff` is the adjunct of `c` along `fromInverseImage`. -/
theorem pushoutCoeff_spec (c : (g^*).obj F ⟶ G) :
    pushoutCoeff g c =
      (pullbackPushforwardAdjunction (fromInverseImage g)).homEquiv
          ((inverseImageTo g)^*.obj F) G
        ((pullbackCompIso (fromInverseImage g) (inverseImageTo g)).inv.app F ≫
          (eqToIso
              (congrArg (fun h : Y ⟶ X ↦ Hom.pullback h)
                (fromInverseImage_comp g))).hom.app F ≫
            c) := rfl

/-- The source of the structure map of `inverseImageAlongI`, as a sheaf of rings on Y. -/
def inverseImageAlongSource (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (𝟙 Y.carrier)).obj
    (inverseImageAlongSpace g SX).sheaf

/-- The structure-sheaf map `g⁻¹ 𝒪_{X'} ⟶ g⁻¹ 𝒪_X` of the thickening `inverseImageAlongI`. -/
def inverseImageAlongISharp (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongSource g SX ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (rfl : 𝟙 Y.carrier = (inverseImageAlongI g SX).hom.base)).hom.app
    (inverseImageAlongSpace g SX).sheaf ≫
  inverseImageStructureSheafHomComm (inverseImageAlongI g SX)

/-- Inclusion of a pulled-back kernel section of `SX` into `g⁻¹ 𝒪_{X'}`. -/
@[expose] private def inverseImageKernelιApp (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m : ((inverseImageTo g)^*.obj F).val.obj U) :
    (inverseImageAlongSource g SX).obj.obj U :=
  (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (rfl : 𝟙 Y.carrier = (inverseImageAlongI g SX).hom.base)).inv.app
    (inverseImageAlongSpace g SX).sheaf |>.hom.app U
    (KernelIdeal.ιApp (inverseImageStructureSheafHomComm (inverseImageAlongI g SX)) U
      (((@inverseImage_isSquareZero _ _ (inverseImageAlongI g SX) (inverseImageAlongI_isFirstOrder g SX)).targetModuleForgetIso
            (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
              (inverseImageStructureSheafHomComm (inverseImageAlongI g SX)) inferInstance
              (@instInverseImage_isLocallySurjective _ _ (inverseImageAlongI g SX)
                (inverseImageAlongI_isFirstOrder g SX).toIsThickening))).hom.hom.app U
        ((@idealModuleToTargetModule _ _ (inverseImageAlongI g SX) (inverseImageAlongI_isFirstOrder g SX)).val.app U
          ((inverseImageAlongKernelComparison g SX).val.app U
            (((inverseImageTo g)^*.map SX.kernelIso.inv).val.app U m)))))

/-- The fibre product `(G ⊕ g⁻¹ 𝒪_X) ×_{g⁻¹ 𝒪_X} g⁻¹ 𝒪_{X'}`. -/
def pushoutProduct (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  let _ := c
  Limits.pullback (SquareZeroSheaf.fst (restrictToInverseImage g G)) (inverseImageAlongISharp g SX)

/-- `pushoutProduct` is the pullback of `fst` along `inverseImageX'AlongTo`. -/
theorem pushoutProduct_eq (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX =
      Limits.pullback (SquareZeroSheaf.fst (restrictToInverseImage g G)) (inverseImageAlongISharp g SX) := rfl

/-- Projection of the fibre product onto `g⁻¹ 𝒪_X ⊕ 𝒢`. -/
def pushoutProduct_fst (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX ⟶ squareZeroSheaf (X := inverseImageSpace g) (restrictToInverseImage g G) :=
  Limits.pullback.fst (SquareZeroSheaf.fst (restrictToInverseImage g G)) (inverseImageAlongISharp g SX)

/-- Projection of the fibre product onto `g⁻¹ 𝒪_{X'}`. -/
def pushoutProduct_snd (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX ⟶ inverseImageAlongSource g SX :=
  Limits.pullback.snd (SquareZeroSheaf.fst (restrictToInverseImage g G)) (inverseImageAlongISharp g SX)

/-- The fibre-product projection onto its common base ring sheaf. -/
def pushoutProduct_toBase (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX ⟶ (inverseImageSpace g).sheaf :=
  pushoutProduct_fst g c SX ≫ SquareZeroSheaf.fst (restrictToInverseImage g G)

/-- The antidiagonal pair has equal components after reduction. -/
private theorem pushoutAntidiagonalSection_condition (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m : ((inverseImageTo g)^*.obj F).val.obj U) :
    (SquareZeroSheaf.fst (restrictToInverseImage g G)).hom.app U
      (TrivSqZeroExt.inr ((pushoutCoeff g c).val.app U m)) =
      (inverseImageAlongISharp g SX).hom.app U (- inverseImageKernelιApp g SX U m) := sorry

/-- The antidiagonal section `(inr (c m), -ι m)` of the fibre product. -/
@[expose] private def pushoutAntidiagonalSection (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m : ((inverseImageTo g)^*.obj F).val.obj U) :
    (pushoutProduct g c SX).obj.obj U :=
  TopCat.Sheaf.CommRing.pullbackSectionMk (SquareZeroSheaf.fst (restrictToInverseImage g G))
    (inverseImageAlongISharp g SX) U
    (TrivSqZeroExt.inr ((pushoutCoeff g c).val.app U m)) (- inverseImageKernelιApp g SX U m)
    (pushoutAntidiagonalSection_condition g c SX U m)

/-- The antidiagonal section map preserves addition. -/
private theorem pushoutAntidiagonalHom_map_add (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m n : ((inverseImageTo g)^*.obj F).val.obj U) :
    pushoutAntidiagonalSection g c SX U (m + n) =
      pushoutAntidiagonalSection g c SX U m + pushoutAntidiagonalSection g c SX U n := sorry

/-- The additive antidiagonal components commute with restrictions. -/
private theorem pushoutAntidiagonalHom_naturality (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    {U V : (Opens Y)ᵒᵖ} (ρ : U ⟶ V) :
    (((restrictionAlong (pushoutProduct_toBase g c SX)).obj
        ((inverseImageTo g)^*.obj F)).val.presheaf.map ρ) ≫
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pushoutAntidiagonalSection g c SX V)
        (pushoutAntidiagonalHom_map_add g c SX V)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pushoutAntidiagonalSection g c SX U)
        (pushoutAntidiagonalHom_map_add g c SX U)) ≫
          (unitModule (Opens.grothendieckTopology Y) (pushoutProduct g c SX)).val.presheaf.map ρ := sorry

/-- The antidiagonal section map respects multiplication by fibre-product sections. -/
private theorem pushoutAntidiagonalHom_map_smul (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (r : (pushoutProduct g c SX).obj.obj U)
    (m : (((restrictionAlong (pushoutProduct_toBase g c SX)).obj
      ((inverseImageTo g)^*.obj F)).val.obj U)) :
    pushoutAntidiagonalSection g c SX U (r • m) = r • pushoutAntidiagonalSection g c SX U m := sorry

/-- The module map sending a pulled-back coefficient to its antidiagonal pair. -/
@[no_expose] def pushoutAntidiagonalHom (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (restrictionAlong (pushoutProduct_toBase g c SX)).obj ((inverseImageTo g)^*.obj F) ⟶
      unitModule (Opens.grothendieckTopology Y) (pushoutProduct g c SX) := by
  exact {
    val := PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (pushoutAntidiagonalSection g c SX U)
          (pushoutAntidiagonalHom_map_add g c SX U))
        naturality {_ _} ρ := pushoutAntidiagonalHom_naturality g c SX ρ }
      (pushoutAntidiagonalHom_map_smul g c SX) }

/-- The antidiagonal ideal sheaf is the image of its coefficient module map. -/
def pushoutAntidiagonal (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Subobject (unitModule (Opens.grothendieckTopology Y) (pushoutProduct g c SX)) :=
  Limits.imageSubobject (pushoutAntidiagonalHom g c SX)

/-- The pushout ring sheaf is the sheafified quotient by the antidiagonal ideal. -/
def pushoutAlongSheaf (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) : TopCat.Sheaf CommRingCat.{u} Y :=
  @IdealSheaf.Quotient.sheaf (Opens Y) inferInstance (Opens.grothendieckTopology Y)
    inferInstance (pushoutProduct g c SX) inferInstance (pushoutAntidiagonal g c SX)

/-- The ringed space with underlying space Y and structure sheaf `𝒪'_1`. -/
def pushoutAlongSpace (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    RingedSpace.{u} :=
  (pushoutAlongSheaf g c SX).toRingedSpace

/-- The common base projection annihilates the antidiagonal ideal. -/
theorem pushoutAntidiagonal_le_ker (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutAntidiagonal g c SX ≤ KernelIdeal.subobject (pushoutProduct_toBase g c SX) := sorry

/-- The projection from the quotient sheaf to its base ring sheaf. -/
def pushoutAlongISharp (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutAlongSheaf g c SX ⟶ (inverseImageSpace g).sheaf :=
  IdealSheaf.Quotient.lift (pushoutAntidiagonal g c SX) (pushoutProduct_toBase g c SX)
    (pushoutAntidiagonal_le_ker g c SX)

/-- The first-order thickening `(Y, g⁻¹ 𝒪_X) ⟶ (Y, 𝒪'_1)`. -/
def pushoutAlongI (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageSpace g ⟶ pushoutAlongSpace g c SX :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (pushoutAlongISharp g c SX).hom }

/-- The thickening `pushoutAlongI` is first-order. -/
private theorem pushoutAlong_i_isFirstOrder (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    IsFirstOrderThickening (pushoutAlongI g c SX) := sorry

/-- The two structure maps to the fibre-product factors have equal reductions. -/
private theorem pushoutAlongSSharp_condition (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (((Hom.StructureSheaf.compIso g f).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
        (inverseImageStructureSheafHomComm f)) ≫ SquareZeroSheaf.inl (restrictToInverseImage g G)) ≫
        SquareZeroSheaf.fst (restrictToInverseImage g G) =
      ((Hom.StructureSheaf.compIso g f).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map (structureMap SX) ≫
      (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
        (Category.id_comp g.hom.base).symm).hom.app (inverseImageX' SX) ≫
      (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
        (𝟙 Y.carrier) g.hom.base).inv.app (inverseImageX' SX)) ≫ inverseImageAlongISharp g SX := sorry

/-- The structure map to the pushout is the compatible sheaf pairing followed by quotient. -/
@[no_expose] def pushoutAlongSSharp (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (g ≫ f).hom.base).obj S.sheaf ⟶
      pushoutAlongSheaf g c SX :=
  Limits.pullback.lift
    (((Hom.StructureSheaf.compIso g f).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
        (inverseImageStructureSheafHomComm f)) ≫ SquareZeroSheaf.inl (restrictToInverseImage g G))
    ((Hom.StructureSheaf.compIso g f).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map (structureMap SX) ≫
      (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
        (Category.id_comp g.hom.base).symm).hom.app (inverseImageX' SX) ≫
      (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
        (𝟙 Y.carrier) g.hom.base).inv.app (inverseImageX' SX)) (pushoutAlongSSharp_condition g c SX) ≫
      IdealSheaf.Quotient.projection (pushoutAntidiagonal g c SX)

/-- The morphism of ringed spaces `(Y, 𝒪'_1) ⟶ S`. -/
def pushoutAlongF' (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutAlongSpace g c SX ⟶ S :=
  InducedCategory.homMk
    { base := (g ≫ f).hom.base
      c :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (g ≫ f).hom.base).homEquiv S.sheaf (pushoutAlongSheaf g c SX)
          (pushoutAlongSSharp g c SX)).hom }

/-- The coefficient pair has equal reductions in the common base. -/
private theorem pushoutAlong_inrSection_condition (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (SquareZeroSheaf.fst (restrictToInverseImage g G)).hom.app U (TrivSqZeroExt.inr n) =
      (inverseImageAlongISharp g SX).hom.app U 0 := sorry

/-- The image of the coefficient pair `(inr n, 0)` in the quotient sheaf. -/
@[expose] private def pushoutAlong_inrSection (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (pushoutAlongSheaf g c SX).obj.obj U :=
  (IdealSheaf.Quotient.projection (pushoutAntidiagonal g c SX)).hom.app U
    (TopCat.Sheaf.CommRing.pullbackSectionMk (SquareZeroSheaf.fst (restrictToInverseImage g G))
      (inverseImageAlongISharp g SX) U (TrivSqZeroExt.inr n) 0
      (pushoutAlong_inrSection_condition g c SX U n))

/-- The coefficient insertion has zero base projection. -/
private theorem pushoutAlongPushforwardToKernel_mem (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    pushoutAlong_inrSection g c SX U n ∈
      KernelIdeal.sectionIdeal (commRingSheafPushforwardMap (pushoutAlongI g c SX)) U := sorry

/-- The coefficient insertion, viewed as a section of the kernel sheaf. -/
@[expose] private def pushoutAlongPushforwardToKernelApp (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U :=
  (KernelIdeal.sectionsIso (commRingSheafPushforwardMap (pushoutAlongI g c SX)) U).inv
    ⟨pushoutAlong_inrSection g c SX U n, pushoutAlongPushforwardToKernel_mem g c SX U n⟩

/-- The coefficient insertion into the kernel is additive. -/
private theorem pushoutAlongPushforwardToKernel_map_add (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m n : G.val.obj U) :
    pushoutAlongPushforwardToKernelApp g c SX U (m + n) =
      pushoutAlongPushforwardToKernelApp g c SX U m +
        pushoutAlongPushforwardToKernelApp g c SX U n := sorry

/-- The additive coefficient insertions commute with restrictions. -/
private theorem pushoutAlongPushforwardToKernel_naturality (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    {U V : (Opens Y)ᵒᵖ} (ρ : U ⟶ V) :
    (((pushoutAlongI g c SX) _*).obj (restrictToInverseImage g G)).val.presheaf.map ρ ≫
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pushoutAlongPushforwardToKernelApp g c SX V)
        (pushoutAlongPushforwardToKernel_map_add g c SX V)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mk' (pushoutAlongPushforwardToKernelApp g c SX U)
        (pushoutAlongPushforwardToKernel_map_add g c SX U)) ≫
          (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.presheaf.map ρ := sorry

/-- The coefficient insertion respects multiplication by quotient-sheaf sections. -/
private theorem pushoutAlongPushforwardToKernel_map_smul (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (r : (pushoutAlongSpace g c SX).ringCatSheaf.obj.obj U)
    (n : (((pushoutAlongI g c SX) _*).obj (restrictToInverseImage g G)).val.obj U) :
    pushoutAlongPushforwardToKernelApp g c SX U (r • n) =
      r • pushoutAlongPushforwardToKernelApp g c SX U n := sorry

/-- The coefficient inclusion into the kernel of the quotient sheaf. -/
@[no_expose] def pushoutAlongPushforwardToKernel (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    ((pushoutAlongI g c SX) _*).obj (restrictToInverseImage g G) ⟶ Hom.kernelIdealSheaf (pushoutAlongI g c SX) := by
  exact {
    val := PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
          (pushoutAlongPushforwardToKernelApp g c SX U)
          (pushoutAlongPushforwardToKernel_map_add g c SX U))
        naturality {_ _} ρ := pushoutAlongPushforwardToKernel_naturality g c SX ρ }
      (pushoutAlongPushforwardToKernel_map_smul g c SX) }

/-- The adjunct of the coefficient insertion into the kernel. -/
@[no_expose] def pushoutAlongKernelInv (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    restrictToInverseImage g G ⟶ Hom.idealModule (pushoutAlongI g c SX) :=
  (@asIso _ _ _ _
      ((pullbackPushforwardAdjunction (pushoutAlongI g c SX)).counit.app
        (restrictToInverseImage g G))
      (@instIsIso_counit_app _ _ _ (pushoutAlong_i_isFirstOrder g c SX).toIsThickening _)).inv ≫
    ((pushoutAlongI g c SX)^*).map (pushoutAlongPushforwardToKernel g c SX)

/-- The coefficient inclusion identifies the coefficient module with the pulled-back kernel. -/
private theorem pushoutAlongKernelInv_isIso (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    IsIso (pushoutAlongKernelInv g c SX) := sorry

/-- The kernel isomorphism is inverse to the specified coefficient insertion. -/
@[no_expose] def pushoutAlongKernelIso (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Hom.idealModule (pushoutAlongI g c SX) ≅ restrictToInverseImage g G :=
  (@asIso _ _ _ _ (pushoutAlongKernelInv g c SX) (pushoutAlongKernelInv_isIso g c SX)).symm

/-- The kernel isomorphism recovers each inserted coefficient. -/
theorem pushoutAlongKernelIso_inr (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutAlongKernelInv g c SX ≫ (pushoutAlongKernelIso g c SX).hom = 𝟙 _ := sorry

/-- The kernel sheaf maps back to the coefficient pushforward by the kernel isomorphism. -/
@[no_expose] def pushoutAlongKernelToPushforward (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Hom.kernelIdealSheaf (pushoutAlongI g c SX) ⟶
      ((pushoutAlongI g c SX) _*).obj (restrictToInverseImage g G) :=
  (@kernelIdealPushforwardIso _ _ (pushoutAlongI g c SX)
      (pushoutAlong_i_isFirstOrder g c SX)).hom ≫
    ((pushoutAlongI g c SX) _*).map (pushoutAlongKernelIso g c SX).hom

/-- The pushout thickening and its ambient map commute over S. -/
private theorem pushoutAlong_commutes (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutAlongI g c SX ≫ pushoutAlongF' g c SX = (inverseImageTo g ≫ f) ≫ 𝟙 S := sorry

/-- The pushout solution induces the prescribed zero identity-base kernel map. -/
private theorem pushoutAlong_induces (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    kernelMapOf (𝟙 S) (inverseImageTo g ≫ f) (pushoutAlongI g c SX)
      (pushoutAlong_i_isFirstOrder g c SX) (pushoutAlongF' g c SX) (pushoutAlong_commutes g c SX) ≫
      ((inverseImageTo g ≫ f) _*).map (pushoutAlongKernelIso g c SX).hom =
        zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G) := sorry

/-- Pushout of 0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 along `c : g^* F ⟶ G`, as a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension of g⁻¹ 𝒪_X by G. -/
def pushoutAlong (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Solution (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
      (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G)) :=
  @Solution.of _ _ _ (𝟙 S) inferInstance (inverseImageTo g ≫ f) (restrictToInverseImage g G)
    (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G))
    _ (pushoutAlongI g c SX) (by exact pushoutAlong_i_isFirstOrder g c SX)
    (pushoutAlongF' g c SX) (by exact pushoutAlong_commutes g c SX)
    (pushoutAlongKernelIso g c SX) (by exact pushoutAlong_induces g c SX)

/-- The projection 𝒪'_1 ⟶ g⁻¹ 𝒪_X is the quotient of the first projection of
the fibre product `(G ⊕ g⁻¹ 𝒪_X) ×_{g⁻¹ 𝒪_X} g⁻¹ 𝒪_{X'}`. -/
theorem pushoutAlong_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (pushoutAlong g c SX).i = pushoutAlongI g c SX ∧
      (pushoutAlong g c SX).f' = pushoutAlongF' g c SX ∧
        (pushoutAlong g c SX).kernelIso = pushoutAlongKernelIso g c SX := ⟨rfl, rfl, rfl⟩

/-- Pairing a section with its scalar inclusion respects the common base projection. -/
private theorem pushoutAlongFromMiddle_condition (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (inverseImageAlongISharp g SX ≫ SquareZeroSheaf.inl (restrictToInverseImage g G)) ≫
        SquareZeroSheaf.fst (restrictToInverseImage g G) =
      (𝟙 (inverseImageAlongSource g SX)) ≫ inverseImageAlongISharp g SX := sorry

/-- The sheaf map to the pushout pairs a section with its scalar image and takes its quotient. -/
@[no_expose] def pushoutAlongFromMiddle (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongSource g SX ⟶ pushoutAlongSheaf g c SX :=
  Limits.pullback.lift
    (inverseImageAlongISharp g SX ≫ SquareZeroSheaf.inl (restrictToInverseImage g G))
    (𝟙 (inverseImageAlongSource g SX)) (pushoutAlongFromMiddle_condition g c SX) ≫
      IdealSheaf.Quotient.projection (pushoutAntidiagonal g c SX)

end AlgebraicGeometry.RingedSpace.Thickening.Solution
