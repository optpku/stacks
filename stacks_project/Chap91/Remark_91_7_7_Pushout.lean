module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap91.Lemma_91_7_1_Diagram
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
public import stacks_project.Chap91.Lemma_91_7_3_Translate
public import stacks_project.Chap91.Lemma_91_7_4
public import stacks_project.Chap91.Remark_91_7_5_Presentation
public import stacks_project.Chap91.Remark_91_7_7_InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import stacks_project.Chap91.«91_4_5_1_SquareZero»

/-!
# Pushout of a square-zero identity-base ringed-space extension

Given 0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 and c : g^* F ⟶ G, the source constructs
𝒪'_1 as the sectionwise antidiagonal quotient of
(G ⊕ g⁻¹ 𝒪_X) ×_{g⁻¹ 𝒪_X} g⁻¹ 𝒪_{X'}, as a square-zero g⁻¹ f⁻¹ 𝒪_S-algebra
extension of g⁻¹ 𝒪_X by G.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open TopologicalSpace TrivSqZeroExt
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X Y : RingedSpace.{u}} {f : X ⟶ S}
variable {F : X.Modules} {G : Y.Modules}

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

variable (g : Y ⟶ X)

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
instance instIsFirstOrderThickening_inverseImageAlongI
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
theorem inverseImageAlongI_comp_toX' (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
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
    (kernelMapOf SX.i (inverseImageTo g) (inverseImageAlongI g SX) inferInstance
      (inverseImageAlongToX' g SX) (inverseImageAlongI_comp_toX' g SX))

/-- `inverseImageAlongKernelComparison` is an isomorphism of kernel modules. -/
instance instIsIso_inverseImageAlongKernelComparison
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    IsIso (inverseImageAlongKernelComparison g SX) := sorry

/-- `inverseImageAlongKernelComparison` is the adjunct of `kernelMapOf` for
`inverseImageAlongToX'`. -/
theorem inverseImageAlongKernelComparison_spec
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongKernelComparison g SX =
      ((pullbackPushforwardAdjunction (inverseImageTo g)).homEquiv
          (Hom.idealModule SX.i) (Hom.idealModule (inverseImageAlongI g SX))).symm
        (kernelMapOf SX.i (inverseImageTo g) (inverseImageAlongI g SX) inferInstance
          (inverseImageAlongToX' g SX) (inverseImageAlongI_comp_toX' g SX)) := sorry

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
            c) := sorry

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
      (show 𝟙 Y.carrier = (inverseImageAlongI g SX).hom.base from rfl)).hom.app
    (inverseImageAlongSpace g SX).sheaf ≫
  inverseImageStructureSheafHomComm (inverseImageAlongI g SX)

/-- Inclusion of a pulled-back kernel section of `SX` into `g⁻¹ 𝒪_{X'}`. -/
def inverseImageKernelιApp (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m : ((inverseImageTo g)^*.obj F).val.obj U) :
    (inverseImageAlongSource g SX).obj.obj U :=
  (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (show 𝟙 Y.carrier = (inverseImageAlongI g SX).hom.base from rfl)).inv.app
    (inverseImageAlongSpace g SX).sheaf |>.hom.app U
    (KernelIdeal.ιApp (inverseImageStructureSheafHomComm (inverseImageAlongI g SX)) U
      (((inverseImage_isSquareZero (inverseImageAlongI g SX)).targetModuleForgetIso
            (inferInstance : IsIso (KernelIdeal.quotientComparison
              (inverseImageStructureSheafHomComm (inverseImageAlongI g SX))))).hom.hom.app U
        ((idealModuleToTargetModule (inverseImageAlongI g SX)).val.app U
          ((inverseImageAlongKernelComparison g SX).val.app U
            (((inverseImageTo g)^*.map SX.kernelIso.inv).val.app U m)))))


/-- The `g⁻¹ 𝒪_X(U)`-action on sections of `𝒢` obtained by restriction of scalars
along `g^♯`. -/
instance instModule_pushoutSection (U : (Opens Y)ᵒᵖ) :
    Module (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.obj U)
      (G.val.obj U) :=
  Module.compHom (G.val.obj U) ((inverseImageStructureSheafHomComm g).hom.app U).hom

/-- Opposite-scalar `g⁻¹ 𝒪_X(U)`-action on sections of `𝒢`. -/
-- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs
-- `Module Rᵐᵒᵖ` keyed by the local evaluation ring of `g⁻¹ 𝒪_X`.
instance instModuleOp_pushoutSection (U : (Opens Y)ᵒᵖ) :
    Module (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.obj U)ᵐᵒᵖ
      (G.val.obj U) :=
  Module.compHom (G.val.obj U)
    (((inverseImageStructureSheafHomComm g).hom.app U).hom.fromOpposite fun x y ↦
      mul_comm (((inverseImageStructureSheafHomComm g).hom.app U).hom x)
        (((inverseImageStructureSheafHomComm g).hom.app U).hom y))

/-- Centrality of the `g⁻¹ 𝒪_X(U)`-action on sections of `𝒢`. -/
-- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs
-- `IsCentralScalar` keyed by the local evaluation ring of `g⁻¹ 𝒪_X`.
instance instIsCentralScalar_pushoutSection (U : (Opens Y)ᵒᵖ) :
    IsCentralScalar
      (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.obj U)
      (G.val.obj U) where
  op_smul_eq_smul := sorry

/-- The trivial square-zero extension of `g⁻¹ 𝒪_X` by `𝒢` on sections over `U`. -/
def pushoutSectionTriv (U : (Opens Y)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of
    (TrivSqZeroExt
      (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.obj U)
      (G.val.obj U))

/-- The first projection of `g⁻¹ 𝒪_X ⊕ 𝒢` as a ring homomorphism. -/
def pushoutFstRingHom (U : (Opens Y)ᵒᵖ) :
    pushoutSectionTriv (G := G) g U →+*
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.obj U where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add

/-- Restriction of a section of `g⁻¹ 𝒪_X ⊕ 𝒢` along a morphism of opens. -/
def pushoutTrivRestriction {U V : (Opens Y)ᵒᵖ} (rho : U ⟶ V) :
    pushoutSectionTriv (G := G) g U ⟶ pushoutSectionTriv (G := G) g V :=
  CommRingCat.ofHom
    { toFun := fun x ↦
        ((((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.map rho
            (TrivSqZeroExt.fst x),
            G.val.map rho (TrivSqZeroExt.snd x)) :
          TrivSqZeroExt
            (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).obj.obj V)
            (G.val.obj V))
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- The presheaf of trivial square-zero extensions `g⁻¹ 𝒪_X ⊕ 𝒢`. -/
def pushoutTrivPresheaf : TopCat.Presheaf CommRingCat.{u} Y where
  obj U := pushoutSectionTriv (G := G) g U
  map rho := pushoutTrivRestriction (G := G) g rho
  map_id U := sorry
  map_comp rho sigma := sorry

/-- The presheaf of trivial square-zero extensions is a sheaf. -/
theorem pushoutTrivPresheaf_isSheaf : (pushoutTrivPresheaf (G := G) g).IsSheaf := sorry

/-- The sheaf of trivial square-zero extensions `g⁻¹ 𝒪_X ⊕ 𝒢`. -/
def pushoutTrivSheaf : TopCat.Sheaf CommRingCat.{u} Y :=
  ⟨pushoutTrivPresheaf (G := G) g, pushoutTrivPresheaf_isSheaf g⟩

/-- The sheaf projection `fst : g⁻¹ 𝒪_X ⊕ 𝒢 ⟶ g⁻¹ 𝒪_X`. -/
def pushoutFstSheaf :
    pushoutTrivSheaf (G := G) g ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (pushoutFstRingHom (G := G) g U)
      naturality {_ _} rho := sorry }

/-- Objectwise identification of a sheaf-level pullback with the pullback of sections. -/
def pushoutPullbackAppIso {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ) :
    (Limits.pullback π ρ).obj.obj U ≅ Limits.pullback (π.hom.app U) (ρ.hom.app U) :=
  ((CategoryTheory.evaluation ((Opens Y)ᵒᵖ) CommRingCat.{u}).obj U).mapIso
      (preservesLimitIso (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
        (cospan π ρ) ≪≫
        HasLimit.isoOfNatIso
          (cospanCompIso (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
            π ρ)) ≪≫
    pullbackObjIso π.hom ρ.hom U

/-- Pairing of compatible sections into a sheaf-level pullback. -/
def pushoutPullbackSectionMk {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : π.hom.app U a = ρ.hom.app U b) :
    (Limits.pullback π ρ).obj.obj U :=
  (pushoutPullbackAppIso π ρ U).inv.hom
    ((IsLimit.conePointUniqueUpToIso
        (limit.isLimit (cospan (π.hom.app U) (ρ.hom.app U)))
        (CommRingCat.pullbackConeIsLimit (π.hom.app U) (ρ.hom.app U))).inv.hom
      ⟨(a, b), h⟩)

/-- The fibre product `(G ⊕ g⁻¹ 𝒪_X) ×_{g⁻¹ 𝒪_X} g⁻¹ 𝒪_{X'}`. -/
def pushoutProduct (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  let _ := c
  Limits.pullback (pushoutFstSheaf (G := G) g) (inverseImageAlongISharp g SX)

/-- `pushoutProduct` is the pullback of `fst` along `inverseImageX'AlongTo`. -/
theorem pushoutProduct_eq (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX =
      Limits.pullback (pushoutFstSheaf (G := G) g) (inverseImageAlongISharp g SX) := sorry

/-- Projection of the fibre product onto `g⁻¹ 𝒪_X ⊕ 𝒢`. -/
def pushoutProduct_fst (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX ⟶ pushoutTrivSheaf (G := G) g :=
  Limits.pullback.fst (pushoutFstSheaf (G := G) g) (inverseImageAlongISharp g SX)

/-- Projection of the fibre product onto `g⁻¹ 𝒪_{X'}`. -/
def pushoutProduct_snd (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutProduct g c SX ⟶ inverseImageAlongSource g SX :=
  Limits.pullback.snd (pushoutFstSheaf (G := G) g) (inverseImageAlongISharp g SX)

/-- The antidiagonal generator `(inr (c m), -ι m)` in the fibre product. -/
def pushoutAntidiagonalSection (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (m : ((inverseImageTo g)^*.obj F).val.obj U) :
    (pushoutProduct g c SX).obj.obj U :=
  pushoutPullbackSectionMk (pushoutFstSheaf (G := G) g) (inverseImageAlongISharp g SX) U
    (TrivSqZeroExt.inr ((pushoutCoeff g c).val.app U m))
    (- inverseImageKernelιApp g SX U m) sorry

/-- The antidiagonal ideal of `(inverseImageTo g)^* F` in the fibre product, generated by
`(inr (c m), -ι m)`. -/
def pushoutAntidiagonal (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) (U : (Opens Y)ᵒᵖ) :
    Ideal ((pushoutProduct g c SX).obj.obj U) :=
  Ideal.span <| Set.range fun m : ((inverseImageTo g)^*.obj F).val.obj U ↦
    pushoutAntidiagonalSection g c SX U m

/-- The section ring of the pushout `𝒪'_1` over `U`. -/
def pushoutSectionRing (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) (U : (Opens Y)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of ((pushoutProduct g c SX).obj.obj U ⧸ pushoutAntidiagonal g c SX U)

/-- Restriction of the pushout section ring along a morphism of opens. -/
def pushoutRestriction (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) {U V : (Opens Y)ᵒᵖ} (rho : U ⟶ V) :
    pushoutSectionRing g c SX U ⟶ pushoutSectionRing g c SX V :=
  CommRingCat.ofHom
    (Ideal.Quotient.lift (pushoutAntidiagonal g c SX U)
      ((Ideal.Quotient.mk (pushoutAntidiagonal g c SX V)).comp
        ((pushoutProduct g c SX).obj.map rho).hom) sorry)

/-- The presheaf of pushout rings `𝒪'_1`. -/
def pushoutPresheaf (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    TopCat.Presheaf CommRingCat.{u} Y where
  obj U := pushoutSectionRing g c SX U
  map rho := pushoutRestriction g c SX rho
  map_id U := sorry
  map_comp rho sigma := sorry

/-- The pushout presheaf of `𝒪'_1` is a sheaf. -/
theorem pushoutPresheaf_isSheaf (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (pushoutPresheaf g c SX).IsSheaf := sorry

/-- The structure sheaf of the pushout `𝒪'_1`. -/
def pushoutAlongSheaf (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  ⟨pushoutPresheaf g c SX, pushoutPresheaf_isSheaf g c SX⟩

/-- The ringed space with underlying space Y and structure sheaf `𝒪'_1`. -/
def pushoutAlongSpace (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    RingedSpace.{u} :=
  (pushoutAlongSheaf g c SX).toRingedSpace

/-- The structure-sheaf map `𝒪'_1 ⟶ g⁻¹ 𝒪_X`. -/
def pushoutAlongISharp (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    pushoutAlongSheaf g c SX ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf :=
  ObjectProperty.homMk
    { app U :=
        CommRingCat.ofHom
          (Ideal.Quotient.lift (pushoutAntidiagonal g c SX U)
            (((pushoutFstSheaf (G := G) g).hom.app U).hom.comp
              ((pushoutProduct_fst g c SX).hom.app U).hom) sorry)
      naturality {_ _} rho := sorry }

/-- The first-order thickening `(Y, g⁻¹ 𝒪_X) ⟶ (Y, 𝒪'_1)`. -/
def pushoutAlongI (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageSpace g ⟶ pushoutAlongSpace g c SX :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (pushoutAlongISharp g c SX).hom }

/-- The thickening `pushoutAlongI` is first-order. -/
instance instIsFirstOrderThickening_pushoutAlong_i (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    IsFirstOrderThickening (pushoutAlongI g c SX) := sorry

/-- The structure map `(g ≫ f)⁻¹ 𝒪_S ⟶ 𝒪'_1`. -/
def pushoutAlongSSharp (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (g ≫ f).hom.base).obj S.sheaf ⟶
      pushoutAlongSheaf g c SX :=
  ObjectProperty.homMk
    { app U :=
        CommRingCat.ofHom
          { toFun := fun a ↦
              Ideal.Quotient.mk (pushoutAntidiagonal g c SX U)
                (pushoutPullbackSectionMk (pushoutFstSheaf (G := G) g)
                  (inverseImageAlongISharp g SX) U
                  (TrivSqZeroExt.inl
                    (((Hom.StructureSheaf.compIso g f).inv ≫
                        (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
                          (inverseImageStructureSheafHomComm f)).hom.app U a))
                  ((((TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
                          (show g.hom.base = 𝟙 Y.carrier ≫ g.hom.base from
                            (Category.id_comp g.hom.base).symm)).hom.app (inverseImageX' SX) ≫
                        (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
                            (𝟙 Y.carrier) g.hom.base).inv.app (inverseImageX' SX)).hom.app U)
                    (((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
                        (structureMap SX)).hom.app U
                      ((Hom.StructureSheaf.compIso g f).inv.hom.app U a))) sorry)
            map_zero' := sorry
            map_one' := sorry
            map_add' := sorry
            map_mul' := sorry }
      naturality {_ _} rho := sorry }

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

/-- The class of `(inr n, 0)` in the algebra pushout. -/
def pushoutAlong_inrSection (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (pushoutAlongSheaf g c SX).obj.obj U :=
  Ideal.Quotient.mk (pushoutAntidiagonal g c SX U)
    (pushoutPullbackSectionMk (pushoutFstSheaf (G := G) g) (inverseImageAlongISharp g SX) U
      (TrivSqZeroExt.inr n) 0 sorry)

/-- A fibre-product representative of a kernel class of the antidiagonal quotient. -/
def pushoutAlongKernelRep (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ)
    (x : (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U) :
    (pushoutProduct g c SX).obj.obj U :=
  Quotient.out
    (KernelIdeal.ιApp (commRingSheafPushforwardMap (pushoutAlongI g c SX)) U x)

/-- `pushoutAlongKernelRep` is `Quotient.out` of the underlying antidiagonal class. -/
theorem pushoutAlongKernelRep_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ)
    (x : (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U) :
    pushoutAlongKernelRep g c SX U x =
      Quotient.out
        (KernelIdeal.ιApp (commRingSheafPushforwardMap (pushoutAlongI g c SX)) U x) :=
  sorry

/-- Kernel section of the second fibre-product component of a kernel class. -/
def pushoutAlongKernelOfSnd (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ)
    (x : (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U) :
    ((inverseImageTo g)^*.obj F).val.obj U :=
  ((inverseImageTo g)^*.map SX.kernelIso.hom).val.app U
    ((asIso (inverseImageAlongKernelComparison g SX)).inv.val.app U
      ((targetModuleToIdealModule (inverseImageAlongI g SX)).val.app U
        (((inverseImage_isSquareZero (inverseImageAlongI g SX)).targetModuleForgetIso
              (inferInstance : IsIso (KernelIdeal.quotientComparison
                (inverseImageStructureSheafHomComm
                  (inverseImageAlongI g SX))))).inv.hom.app U
          ((KernelIdeal.sectionsIso
                (inverseImageStructureSheafHomComm (inverseImageAlongI g SX)) U).inv
            ⟨((TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
                  (show 𝟙 Y.carrier = (inverseImageAlongI g SX).hom.base from
                    rfl)).hom.app (inverseImageAlongSpace g SX).sheaf).hom.app U
                ((pushoutProduct_snd g c SX).hom.app U
                  (pushoutAlongKernelRep g c SX U x)),
              sorry⟩))))

/-- `pushoutAlongKernelOfSnd` recovers the `F`-section from the second component. -/
theorem pushoutAlongKernelOfSnd_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ)
    (x : (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U) :
    pushoutAlongKernelOfSnd g c SX U x =
      ((inverseImageTo g)^*.map SX.kernelIso.hom).val.app U
        ((asIso (inverseImageAlongKernelComparison g SX)).inv.val.app U
          ((targetModuleToIdealModule (inverseImageAlongI g SX)).val.app U
            (((inverseImage_isSquareZero (inverseImageAlongI g SX)).targetModuleForgetIso
                  (inferInstance : IsIso (KernelIdeal.quotientComparison
                    (inverseImageStructureSheafHomComm
                      (inverseImageAlongI g SX))))).inv.hom.app U
              ((KernelIdeal.sectionsIso
                    (inverseImageStructureSheafHomComm (inverseImageAlongI g SX)) U).inv
                ⟨((TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
                      (show 𝟙 Y.carrier = (inverseImageAlongI g SX).hom.base from
                        rfl)).hom.app (inverseImageAlongSpace g SX).sheaf).hom.app U
                    ((pushoutProduct_snd g c SX).hom.app U
                      (pushoutAlongKernelRep g c SX U x)),
                  sorry⟩)))) :=
  sorry

/-- The `G`-component of a genuine kernel class of the antidiagonal quotient:
`snd(fst r) + pushoutCoeff(kernel of snd r)` on `Quotient.out` of the class. -/
def pushoutAlongKernelCoeffApp (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ)
    (x : (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U) :
    G.val.obj U :=
  let r := pushoutAlongKernelRep g c SX U x
  let n : G.val.obj U :=
    (pushoutCoeff g c).val.app U (pushoutAlongKernelOfSnd g c SX U x)
  TrivSqZeroExt.snd ((pushoutProduct_fst g c SX).hom.app U r) + n

/-- `pushoutAlongKernelCoeffApp` is `snd(fst r) + pushoutCoeff(kernel of snd r)`
on `Quotient.out` of a kernel class. -/
theorem pushoutAlongKernelCoeffApp_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (U : (Opens Y)ᵒᵖ)
    (x : (Hom.kernelIdealSheaf (pushoutAlongI g c SX)).val.obj U) :
    pushoutAlongKernelCoeffApp g c SX U x =
      (let n : G.val.obj U :=
        (pushoutCoeff g c).val.app U (pushoutAlongKernelOfSnd g c SX U x)
      TrivSqZeroExt.snd
          ((pushoutProduct_fst g c SX).hom.app U (pushoutAlongKernelRep g c SX U x)) +
        n) :=
  sorry

/-- The `𝒪'_1`-module map `Ker((pushoutAlongI)^♯) ⟶ (pushoutAlongI)_* G` given by
`snd(fst r) + pushoutCoeff(kernel of snd r)` on `Quotient.out` of a kernel class. -/
def pushoutAlongKernelToPushforward (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Hom.kernelIdealSheaf (pushoutAlongI g c SX) ⟶
      ((pushoutAlongI g c SX) _*).obj (restrictToInverseImage g G) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk' (pushoutAlongKernelCoeffApp g c SX U) sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- The `𝒪'_1`-module map `(pushoutAlongI)_* G ⟶ Ker((pushoutAlongI)^♯)` sending
`n` to the class of `(inr n, 0)`. -/
def pushoutAlongPushforwardToKernel (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    ((pushoutAlongI g c SX) _*).obj (restrictToInverseImage g G) ⟶
      Hom.kernelIdealSheaf (pushoutAlongI g c SX) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun n ↦
                (KernelIdeal.sectionsIso
                    (commRingSheafPushforwardMap (pushoutAlongI g c SX)) U).inv
                  ⟨pushoutAlong_inrSection g c SX U n, sorry⟩)
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- Identification of `Ker((pushoutAlongI)^♯)` with `restrictToInverseImage g G`. -/
def pushoutAlongKernelIso (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Hom.idealModule (pushoutAlongI g c SX) ≅ restrictToInverseImage g G where
  hom :=
    ((pushoutAlongI g c SX)^*).map (pushoutAlongKernelToPushforward g c SX) ≫
      (pullbackPushforwardAdjunction (pushoutAlongI g c SX)).counit.app
        (restrictToInverseImage g G)
  inv :=
    (asIso
        ((pullbackPushforwardAdjunction (pushoutAlongI g c SX)).counit.app
          (restrictToInverseImage g G))).inv ≫
      ((pushoutAlongI g c SX)^*).map (pushoutAlongPushforwardToKernel g c SX)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pushout of 0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 along `c : g^* F ⟶ G`, as a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension of g⁻¹ 𝒪_X by G. -/
def pushoutAlong (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Solution (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
      (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G)) :=
  Solution.of (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
    (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G))
    (pushoutAlongI g c SX) (pushoutAlongF' g c SX) sorry
    (pushoutAlongKernelIso g c SX) sorry

/-- The projection 𝒪'_1 ⟶ g⁻¹ 𝒪_X is the quotient of the first projection of
the fibre product `(G ⊕ g⁻¹ 𝒪_X) ×_{g⁻¹ 𝒪_X} g⁻¹ 𝒪_{X'}`. -/
theorem pushoutAlong_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (pushoutAlong g c SX).i = pushoutAlongI g c SX ∧
      (pushoutAlong g c SX).f' = pushoutAlongF' g c SX ∧
        (pushoutAlong g c SX).kernelIso = pushoutAlongKernelIso g c SX := sorry

/-- The morphism `(Y, g⁻¹ 𝒪_{X'}) ⟶ S`. -/
def inverseImageAlongF' (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongSpace g SX ⟶ S :=
  InducedCategory.homMk
    { base := (g ≫ f).hom.base
      c :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (g ≫ f).hom.base).homEquiv S.sheaf (inverseImageX'Along g SX)
          ((Hom.StructureSheaf.compIso g f).inv ≫
            (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
              (structureMap SX))).hom }

/-- Transport of `c` as a map of kernel ideals from `g⁻¹ 𝒪_{X'}` to the pushout. -/
def pushoutAlongDiagram_ν (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    Hom.idealModule (inverseImageAlongI g SX) ⟶
      ((𝟙 (inverseImageSpace g)) _*).obj (Hom.idealModule (pushoutAlongI g c SX)) :=
  (pullbackPushforwardAdjunction (𝟙 (inverseImageSpace g))).homEquiv
      (Hom.idealModule (inverseImageAlongI g SX))
      (Hom.idealModule (pushoutAlongI g c SX))
    ((Hom.pullbackIdIso (inverseImageSpace g)).hom.app
        (Hom.idealModule (inverseImageAlongI g SX)) ≫
      (asIso (inverseImageAlongKernelComparison g SX)).inv ≫
        (inverseImageTo g)^*.map SX.kernelIso.hom ≫
          pushoutCoeff g c ≫ (pushoutAlongKernelIso g c SX).inv)

/-- The identity-base connecting diagram from `g⁻¹ 𝒪_{X'}` to the pushout along `c`. -/
def pushoutAlongDiagram (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    RelativeDiagram (pushoutAlong g c SX).i (inverseImageTo g ≫ f)
      (pushoutAlong g c SX).f' (𝟙 S)
      (inverseImageAlongI g SX) (inverseImageTo g ≫ f) (inverseImageAlongF' g SX) (𝟙 S)
      (𝟙 (inverseImageSpace g)) (𝟙 S) (𝟙 S) where
  comm := CommDiagram.mk (pushoutAlong g c SX).commutes sorry sorry sorry
  ν := pushoutAlongDiagram_ν g c SX
  comm_kernel := sorry

/-- `pushoutAlongDiagram` has identity maps on `(Y, g⁻¹ 𝒪_X)` and on S, and `ν` is the
transport of `c`. -/
theorem pushoutAlongDiagram_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (pushoutAlongDiagram g c SX).comm.back.w = (pushoutAlong g c SX).commutes ∧
      (pushoutAlongDiagram g c SX).ν = pushoutAlongDiagram_ν g c SX := sorry

/-- The sheaf map `g⁻¹ 𝒪_{X'} ⟶ 𝒪'_1` sending a section `a` to the class of
`(inl (image of a), a)`. -/
def pushoutAlongFromMiddle (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    inverseImageAlongSource g SX ⟶ pushoutAlongSheaf g c SX :=
  ObjectProperty.homMk
    { app U :=
        CommRingCat.ofHom
          { toFun := fun a ↦
              Ideal.Quotient.mk (pushoutAntidiagonal g c SX U)
                (pushoutPullbackSectionMk (pushoutFstSheaf (G := G) g)
                  (inverseImageAlongISharp g SX) U
                  (TrivSqZeroExt.inl ((inverseImageAlongISharp g SX).hom.app U a)) a sorry)
            map_zero' := sorry
            map_one' := sorry
            map_add' := sorry
            map_mul' := sorry }
      naturality {_ _} rho := sorry }

/-- The vertical map `g⁻¹ 𝒪_{X'} ⟶ 𝒪'_1` in the source pushout square. -/
def toPushoutAlong (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    FittingMap (pushoutAlongDiagram g c SX) :=
  FittingMap.of
    (InducedCategory.homMk
      { base := 𝟙 Y.carrier
        c :=
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                (𝟙 Y.carrier)).unit.app (inverseImageAlongSpace g SX).sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (𝟙 Y.carrier)).map
              (pushoutAlongFromMiddle g c SX)).hom })
    sorry sorry sorry

/-- `toPushoutAlong` is compatible with the projections to `g⁻¹ 𝒪_X`. -/
theorem toPushoutAlong_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    (toPushoutAlong g c SX).hom ≫ inverseImageAlongF' g SX =
      (pushoutAlong g c SX).f' := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
