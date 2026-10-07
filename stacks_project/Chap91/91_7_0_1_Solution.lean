module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import stacks_project.Chap91.«91_3_1_1_Arrow»
public import stacks_project.Chap91.Remark_91_4_7_Thickening

/-!
# Solutions of the first-order deformation equation on ringed spaces

Given a first-order thickening t : S ⟶ S', a morphism f : X ⟶ S, an 𝒪_X-module
𝒢, and an f-map c : Ker(t^♯) ⟶ f_* 𝒢, a solution of the displayed 08U7 diagram
is a first-order thickening i : X ⟶ X' together with a morphism of thickenings
(f, f') whose kernel is identified with 𝒢 and which induces c.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S)

/-- The comparison 𝒥 ⟶ f_* ℐ of kernel ideals as 𝒪_S-modules, induced by (f')^♯
along a commutative square of first-order thickenings. -/
def kernelMapOf {X' : RingedSpace.{u}} (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) (f' : X' ⟶ S') (w : i ≫ f' = f ≫ t) :
    RingedSpace.Hom.idealModule t ⟶ (f _*).obj (RingedSpace.Hom.idealModule i) :=
  (RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv
    (RingedSpace.Hom.idealModule t) (RingedSpace.Hom.idealModule i)
    (((RingedSpace.Hom.pullbackCompIso f t).symm ≪≫
        eqToIso (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pullback h) w.symm) ≪≫
        RingedSpace.Hom.pullbackCompIso i f').hom.app
      (RingedSpace.Hom.kernelIdealSheaf t) ≫
      (i^*).map
        (Hom.idealMap
          (homMk f f' w.symm :
            MorphismProperty.Arrow.mk i hi.toIsThickening ⟶ of t)))

/-- The 𝒪_X-module form of an f-map out of the kernel ideal of t. -/
def cPull {G : X.Modules} (c : RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) :
    (f^*).obj (RingedSpace.Hom.idealModule t) ⟶ G :=
  (f^*).map c ≫ (RingedSpace.Hom.pullbackPushforwardAdjunction f).counit.app G

/-- The adjunct of `kernelMapOf` recovers the inverse-image comparison of kernel ideals. -/
theorem kernelMapOf_spec {X' : RingedSpace.{u}} (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) (f' : X' ⟶ S') (w : i ≫ f' = f ≫ t) :
    ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv
        (RingedSpace.Hom.idealModule t) (RingedSpace.Hom.idealModule i)).symm
      (kernelMapOf t f i hi f' w) =
      (((RingedSpace.Hom.pullbackCompIso f t).symm ≪≫
          eqToIso (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pullback h) w.symm) ≪≫
          RingedSpace.Hom.pullbackCompIso i f').hom.app
        (RingedSpace.Hom.kernelIdealSheaf t) ≫
        (i^*).map
          (Hom.idealMap
            (homMk f f' w.symm :
              MorphismProperty.Arrow.mk i hi.toIsThickening ⟶ of t))) := sorry

/-- `cPull` is the adjunct of the given f-map. -/
theorem cPull_spec {G : X.Modules} (c : RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) :
    cPull t f c =
      ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv
        (RingedSpace.Hom.idealModule t) G).symm c :=
  sorry

/-- The kernel-ideal inclusion of a ringed-space morphism is killed by the associated
structure-sheaf map. -/
theorem kernelIdealι_comp_unitToPushforwardObjUnit {Y Y' : RingedSpace.{u}} (h : Y ⟶ Y') :
    RingedSpace.Hom.kernelIdealι h ≫
      SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom h) = 0 :=
  sorry

/-- The known bottom row 0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ t_* 𝒪_S ⟶ 0 of 𝒪_{S'}-modules. -/
abbrev bottomShortComplex : ShortComplex S'.Modules :=
  ShortComplex.mk (RingedSpace.Hom.kernelIdealι t)
    (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom t))
    (kernelIdealι_comp_unitToPushforwardObjUnit t)

/-- The bottom row of the 08U7 diagram is short exact. -/
theorem bottomShortComplex_shortExact : (bottomShortComplex t).ShortExact := sorry

variable (G : X.Modules) (c : RingedSpace.Hom.idealModule t ⟶ (f _*).obj G)

/-- A solution of the 08U7 diagram: a first-order thickening i : X ⟶ X' and a morphism
of thickenings (f, f') whose kernel is identified with 𝒢 and which induces c. -/
structure Solution where
  /-- The unknown middle ringed space X'. -/
  space : RingedSpace.{u}
  /-- The first-order thickening i : X ⟶ X'. -/
  i : X ⟶ space
  /-- The morphism i is a first-order thickening. -/
  [i_isFirstOrder : IsFirstOrderThickening i]
  /-- The morphism f' : X' ⟶ S' on ambient spaces. -/
  f' : space ⟶ S'
  /-- The right-hand square of ringed spaces commutes. -/
  commutes : i ≫ f' = f ≫ t
  /-- Identification of Ker(i^♯) with 𝒢 as 𝒪_X-modules. -/
  kernelIso : RingedSpace.Hom.idealModule i ≅ G
  /-- The induced f-map on kernels equals c. -/
  induces_c :
    kernelMapOf t f i i_isFirstOrder f' commutes ≫ (f _*).map kernelIso.hom = c

namespace Solution

/-- Assemble a solution from a first-order thickening, a morphism to S', a kernel
identification, and the induced-map condition. -/
def of {X' : RingedSpace.{u}} (i : X ⟶ X') [i_isFirstOrder : IsFirstOrderThickening i]
    (f' : X' ⟶ S') (commutes : i ≫ f' = f ≫ t)
    (kernelIso : RingedSpace.Hom.idealModule i ≅ G)
    (induces_c :
      kernelMapOf t f i i_isFirstOrder f' commutes ≫ (f _*).map kernelIso.hom = c) :
    Solution t f G c where
  space := X'
  i := i
  i_isFirstOrder := i_isFirstOrder
  f' := f'
  commutes := commutes
  kernelIso := kernelIso
  induces_c := induces_c

variable {t f G c}

/-- The 𝒪_S-module map on kernels induced by a solution. -/
def kernelMap (sol : Solution t f G c) :
    RingedSpace.Hom.idealModule t ⟶ (f _*).obj (RingedSpace.Hom.idealModule sol.i) :=
  kernelMapOf t f sol.i sol.i_isFirstOrder sol.f' sol.commutes

/-- The top row 0 ⟶ Ker(i^♯) ⟶ 𝒪_{X'} ⟶ i_* 𝒪_X ⟶ 0 of 𝒪_{X'}-modules. -/
abbrev topShortComplex (sol : Solution t f G c) : ShortComplex sol.space.Modules :=
  ShortComplex.mk (RingedSpace.Hom.kernelIdealι sol.i)
    (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom sol.i))
    (kernelIdealι_comp_unitToPushforwardObjUnit sol.i)

/-- The top row of a solution is short exact. -/
theorem topShortComplex_shortExact (sol : Solution t f G c) :
    (topShortComplex sol).ShortExact := sorry

/-- The morphism of thickenings (f, f') occupying the right-hand square. -/
def toArrowHom (sol : Solution t f G c) :
    MorphismProperty.Arrow.mk sol.i sol.i_isFirstOrder.toIsThickening ⟶
      Thickening.of t :=
  homMk f sol.f' sol.commutes.symm

/-- The filled module diagram of a solution, as a morphism of short complexes of
𝒪_{S'}-modules, after pushing the top row forward along f'. -/
def toHom (sol : Solution t f G c) :
    (bottomShortComplex t).Hom ((topShortComplex sol).map (sol.f' _*)) where
  τ₁ :=
    (RingedSpace.Hom.pullbackPushforwardAdjunction sol.f').homEquiv
      (RingedSpace.Hom.kernelIdealSheaf t) (RingedSpace.Hom.kernelIdealSheaf sol.i)
      (Hom.idealMap (toArrowHom sol))
  τ₂ :=
    SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom sol.f')
  τ₃ :=
    (t _*).map
        (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom f)) ≫
      (RingedSpace.Hom.pushforwardCompIso f t).inv.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (eqToIso
          (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pushforward h)
            sol.commutes.symm)).hom.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (RingedSpace.Hom.pushforwardCompIso sol.i sol.f').hom.app
        (SheafOfModules.unit X.ringCatSheaf)
  comm₁₂ := sorry
  comm₂₃ := sorry

/-- A solution is a first-order thickening of X whose structure map to S' commutes with
f and t and induces c on kernels. -/
theorem spec (sol : Solution t f G c) :
    IsFirstOrderThickening sol.i ∧
      sol.i ≫ sol.f' = f ≫ t ∧
        kernelMap sol ≫ (f _*).map sol.kernelIso.hom = c := sorry

/-- The identification of kernels induces the given f-map c. -/
theorem induces_c_eq (sol : Solution t f G c) :
    kernelMap sol ≫ (f _*).map sol.kernelIso.hom = c := sorry

/-- The two squares of `toHom` commute. -/
theorem toHom_comm (sol : Solution t f G c) :
    (toHom sol).τ₁ ≫ ((topShortComplex sol).map (sol.f' _*)).f =
        (bottomShortComplex t).f ≫ (toHom sol).τ₂ ∧
      (toHom sol).τ₂ ≫ ((topShortComplex sol).map (sol.f' _*)).g =
        (bottomShortComplex t).g ≫ (toHom sol).τ₃ :=
  sorry

end Solution

end AlgebraicGeometry.RingedSpace.Thickening
