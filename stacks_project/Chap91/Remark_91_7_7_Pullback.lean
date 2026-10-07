module

public import Mathlib.Algebra.Category.Ring.Constructions
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

/-!
# Pullback of a square-zero identity-base ringed-space extension

Given 0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 and g^♯ : g⁻¹ 𝒪_X ⟶ 𝒪_Y, the source
constructs 𝒪'_2 = i⁻¹ 𝒪_{Y'} ×_{𝒪_Y} g⁻¹ 𝒪_X as a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension of g⁻¹ 𝒪_X by G.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open TopologicalSpace Opposite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X Y : RingedSpace.{u}} {f : X ⟶ S}
variable {F : X.Modules} {G : Y.Modules}
variable (g : Y ⟶ X)

/-- Objectwise identification of a sheaf-level pullback with the pullback of sections. -/
def pullbackAppIso {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
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
def pullbackSectionMk {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : π.hom.app U a = ρ.hom.app U b) :
    (Limits.pullback π ρ).obj.obj U :=
  (pullbackAppIso π ρ U).inv.hom
    ((IsLimit.conePointUniqueUpToIso
        (limit.isLimit (cospan (π.hom.app U) (ρ.hom.app U)))
        (CommRingCat.pullbackConeIsLimit (π.hom.app U) (ρ.hom.app U))).inv.hom
      ⟨(a, b), h⟩)

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
instance instIsFirstOrderThickening_pullbackAlong_i
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    IsFirstOrderThickening (pullbackAlongI g SY) := sorry

/-- The structure-sheaf projection `𝒪'_2 ⟶ i⁻¹ 𝒪_{Y'}`. -/
def pullbackAlongFst (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlongSheaf g SY ⟶ inverseImageX' SY :=
  Limits.pullback.fst (inverseImageStructureSheafHomComm SY.i)
    (inverseImageStructureSheafHomComm g)

/-- The structure map `(g ≫ f)⁻¹ 𝒪_S ⟶ 𝒪'_2` induced by the two maps to
`i⁻¹ 𝒪_{Y'}` and `g⁻¹ 𝒪_X`. -/
def pullbackAlongSSharp (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (g ≫ f).hom.base).obj S.sheaf ⟶
      pullbackAlongSheaf g SY :=
  Limits.pullback.lift (structureMap SY)
    ((Hom.StructureSheaf.compIso g f).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).map
        (inverseImageStructureSheafHomComm f))
    sorry

/-- The morphism of ringed spaces `(Y, 𝒪'_2) ⟶ S`. -/
def pullbackAlongF' (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlongSpace g SY ⟶ S :=
  InducedCategory.homMk
    { base := (g ≫ f).hom.base
      c :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (g ≫ f).hom.base).homEquiv S.sheaf (pullbackAlongSheaf g SY)
          (pullbackAlongSSharp g SY)).hom }

/-- The `𝒪'_2`-module map `Ker((pullbackAlongI)^♯) ⟶ (pullbackAlongI)_* G` reading the
first fibre-product component through `SY.kernelIso`. -/
def pullbackAlongKernelToPushforward
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Hom.kernelIdealSheaf (pullbackAlongI g SY) ⟶
      ((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun x ↦
                (SY.kernelIso.hom).val.app U
                  ((targetModuleToIdealModule SY.i).val.app U
                    (((inverseImage_isSquareZero SY.i).targetModuleForgetIso
                          (inferInstance : IsIso (KernelIdeal.quotientComparison
                            (inverseImageStructureSheafHomComm SY.i)))).inv.hom.app U
                      ((KernelIdeal.sectionsIso
                            (inverseImageStructureSheafHomComm SY.i) U).inv
                        ⟨(pullbackAlongFst g SY).hom.app U
                            (KernelIdeal.ιApp
                              (commRingSheafPushforwardMap (pullbackAlongI g SY)) U x),
                          sorry⟩))))
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- Inclusion of a coefficient of `G` into `i⁻¹ 𝒪_{Y'}`. -/
def pullbackAlongKernelιApp
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (U : (Opens Y)ᵒᵖ) (n : G.val.obj U) :
    (inverseImageX' SY).obj.obj U :=
  KernelIdeal.ιApp (inverseImageStructureSheafHomComm SY.i) U
    (((inverseImage_isSquareZero SY.i).targetModuleForgetIso
          (inferInstance : IsIso (KernelIdeal.quotientComparison
            (inverseImageStructureSheafHomComm SY.i)))).hom.hom.app U
      ((idealModuleToTargetModule SY.i).val.app U ((SY.kernelIso.inv).val.app U n)))

/-- The `𝒪'_2`-module map `(pullbackAlongI)_* G ⟶ Ker((pullbackAlongI)^♯)` sending `n`
to the class of `(ι n, 0)`. -/
def pullbackAlongPushforwardToKernel
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    ((pullbackAlongI g SY) _*).obj (restrictToInverseImage g G) ⟶
      Hom.kernelIdealSheaf (pullbackAlongI g SY) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun n ↦
                (KernelIdeal.sectionsIso
                    (commRingSheafPushforwardMap (pullbackAlongI g SY)) U).inv
                  ⟨pullbackSectionMk (inverseImageStructureSheafHomComm SY.i)
                      (inverseImageStructureSheafHomComm g) U
                      (pullbackAlongKernelιApp g SY U n) 0 sorry,
                    sorry⟩)
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- Identification of `Ker((pullbackAlongI)^♯)` with `restrictToInverseImage g G`. -/
def pullbackAlongKernelIso
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Hom.idealModule (pullbackAlongI g SY) ≅ restrictToInverseImage g G where
  hom :=
    ((pullbackAlongI g SY)^*).map (pullbackAlongKernelToPushforward g SY) ≫
      (pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
        (restrictToInverseImage g G)
  inv :=
    (asIso
        ((pullbackPushforwardAdjunction (pullbackAlongI g SY)).counit.app
          (restrictToInverseImage g G))).inv ≫
      ((pullbackAlongI g SY)^*).map (pullbackAlongPushforwardToKernel g SY)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pullback of 0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 along g^♯, as a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension of g⁻¹ 𝒪_X by G. -/
def pullbackAlong (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Solution (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
      (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G)) :=
  Solution.of (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
    (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G))
    (pullbackAlongI g SY) (pullbackAlongF' g SY) sorry
    (pullbackAlongKernelIso g SY) sorry

/-- The projection 𝒪'_2 ⟶ g⁻¹ 𝒪_X is the second projection of the sheaf
fibre product. -/
theorem pullbackAlong_spec (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (pullbackAlong g SY).i = pullbackAlongI g SY ∧
      (pullbackAlong g SY).f' = pullbackAlongF' g SY ∧
        (pullbackAlong g SY).kernelIso = pullbackAlongKernelIso g SY := sorry

/-- `fromInverseImage` of a first-order thickening is again first-order. -/
instance instIsFirstOrderThickening_fromInverseImage_sol
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    IsFirstOrderThickening (fromInverseImage SY.i) := sorry

/-- Comparison `Ker(SY.i) ⟶ Ker(fromInverseImage SY.i)` induced by
`inverseImageTo SY.i`. -/
def fromInverseImageKernelComparison
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Hom.idealModule SY.i ⟶ Hom.idealModule (fromInverseImage SY.i) :=
  (Hom.pullbackIdIso Y).inv.app (Hom.idealModule SY.i) ≫
    ((pullbackPushforwardAdjunction (𝟙 Y)).homEquiv
        (Hom.idealModule SY.i) (Hom.idealModule (fromInverseImage SY.i))).symm
      (kernelMapOf SY.i (𝟙 Y) (fromInverseImage SY.i) inferInstance
        (inverseImageTo SY.i) (fromInverseImage_comp SY.i))

/-- Identity transport of `G` as a map of kernel ideals from the pullback to
`(Y, i⁻¹ 𝒪_{Y'})`. -/
def pullbackAlongDiagram_ν
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Hom.idealModule (pullbackAlongI g SY) ⟶
      ((fromInverseImage g)_*).obj (Hom.idealModule (fromInverseImage SY.i)) :=
  (pullbackAlongKernelIso g SY).hom ≫
    ((fromInverseImage g)_*).map
      (SY.kernelIso.inv ≫ fromInverseImageKernelComparison g SY)

/-- The identity-base connecting diagram from `(Y, i⁻¹ 𝒪_{Y'})` to the pullback along g^♯. -/
def pullbackAlongDiagram (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    RelativeDiagram (fromInverseImage SY.i) (g ≫ f) (inverseImageTo SY.i ≫ SY.f') (𝟙 S)
      (pullbackAlong g SY).i (inverseImageTo g ≫ f) (pullbackAlong g SY).f' (𝟙 S)
      (fromInverseImage g) (𝟙 S) (𝟙 S) where
  comm := CommDiagram.mk sorry sorry sorry sorry
  ν := pullbackAlongDiagram_ν g SY
  comm_kernel := sorry

/-- `pullbackAlongDiagram` has vertical map `fromInverseImage g` and identity maps
on S. -/
theorem pullbackAlongDiagram_spec
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (pullbackAlongDiagram g SY).comm.front.w = (pullbackAlong g SY).commutes := sorry

/-- The morphism of ringed spaces `(Y, i⁻¹ 𝒪_{Y'}) ⟶ (Y, 𝒪'_2)` with identity
underlying map and structure map `𝒪'_2 ⟶ i⁻¹ 𝒪_{Y'}`. -/
def fromPullbackAlongHom
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    inverseImageSpace SY.i ⟶ pullbackAlongSpace g SY :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (pullbackAlongFst g SY).hom }

/-- The vertical map 𝒪'_2 ⟶ 𝒪_{Y'} in the source pullback square, as a morphism
of ringed spaces Y' ⟶ (Y, 𝒪'_2). -/
def fromPullbackAlong (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    FittingMap (pullbackAlongDiagram g SY) :=
  FittingMap.of (fromPullbackAlongHom g SY) sorry sorry sorry

/-- `fromPullbackAlong` is compatible with the projections to 𝒪_Y and g⁻¹ 𝒪_X. -/
theorem fromPullbackAlong_spec
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (fromPullbackAlong g SY).hom ≫ (pullbackAlong g SY).f' =
        inverseImageTo SY.i ≫ SY.f' ∧
      fromInverseImage SY.i ≫ (fromPullbackAlong g SY).hom =
        fromInverseImage g ≫ (pullbackAlong g SY).i := sorry

/-- The underlying map of sheaves of sets `𝒪'_2 ⟶ i⁻¹ 𝒪_{Y'}`. -/
def pullbackAlong_presentation
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (sheafForget (Opens.grothendieckTopology Y)).obj (pullbackAlongSheaf g SY) ⟶
      (sheafForget (Opens.grothendieckTopology Y)).obj (inverseImageX' SY) :=
  (sheafForget (Opens.grothendieckTopology Y)).map (pullbackAlongFst g SY)

/-- `pullbackAlong_presentation` is `sheafForget` of the first fibre-product projection. -/
theorem pullbackAlong_presentation_spec
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    pullbackAlong_presentation g SY =
      (sheafForget (Opens.grothendieckTopology Y)).map (pullbackAlongFst g SY) := sorry

/-- A presentation assignment to `i⁻¹ 𝒪_{Y'}` lifts through `𝒪'_2` after pairing with an
assignment to `g⁻¹ 𝒪_X` (source diagrams E, E', φ). -/
theorem pullbackAlong_presentationLift
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G))
    (E : Sheaf (Opens.grothendieckTopology Y) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology Y)).obj (inverseImageX' SY))
    (α : E ⟶ (sheafForget (Opens.grothendieckTopology Y)).obj
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)) :
    ∃ lift : E ⟶ (sheafForget (Opens.grothendieckTopology Y)).obj (pullbackAlongSheaf g SY),
      lift ≫ pullbackAlong_presentation g SY = α' ∧
        lift ≫ (sheafForget (Opens.grothendieckTopology Y)).map (pullbackAlongISharp g SY) =
          α := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
