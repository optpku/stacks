module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.KernelMap

/-!
# Solutions of first-order deformation diagrams on ringed spaces

A solution consists of a first-order thickening together with a compatible morphism to a
fixed first-order thickening and an identification of the kernel module.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S)

/-- The short complex formed by the kernel ideal inclusion and structure-sheaf map of a
first-order thickening. -/
abbrev bottomShortComplex : ShortComplex S'.Modules :=
  ShortComplex.mk (RingedSpace.Hom.kernelIdealι t)
    (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom t))
    (CategoryTheory.Limits.kernelSubobject_arrow_comp
      (SheafOfModules.RingedSite.KernelIdeal.map
        (RingedSpace.Hom.commRingSheafPushforwardMap t)))

/-- The bottom kernel short complex is short exact. -/
theorem bottomShortComplex_shortExact : (bottomShortComplex t).ShortExact := sorry

variable (G : X.Modules) (c : RingedSpace.Hom.idealModule t ⟶ (f _*).obj G)

/-- A solution is a first-order thickening of `X` equipped with a compatible ambient map and
an isomorphism from its kernel ideal module to `G` inducing `c`. -/
structure Solution where
  /-- The ambient ringed space of the solution. -/
  space : RingedSpace.{u}
  /-- The first-order thickening inclusion. -/
  i : X ⟶ space
  /-- The inclusion is a first-order thickening. -/
  [i_isFirstOrder : IsFirstOrderThickening i]
  /-- The ambient map to `S'`. -/
  f' : space ⟶ S'
  /-- The square with `f` and `t` commutes. -/
  commutes : i ≫ f' = f ≫ t
  /-- The kernel ideal module is identified with `G`. -/
  kernelIso : RingedSpace.Hom.idealModule i ≅ G
  /-- The induced map on kernels is `c`. -/
  induces_c :
    kernelMapOf t f i i_isFirstOrder f' commutes ≫ (f _*).map kernelIso.hom = c

namespace Solution

/-- Construct a solution from its thickening, ambient map, kernel identification, and induced
kernel-map condition. -/
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

/-- The map on kernel modules induced by a solution. -/
def kernelMap (sol : Solution t f G c) :
    RingedSpace.Hom.idealModule t ⟶ (f _*).obj (RingedSpace.Hom.idealModule sol.i) :=
  kernelMapOf t f sol.i sol.i_isFirstOrder sol.f' sol.commutes

/-- The short complex formed by the kernel ideal inclusion and structure-sheaf map of the
solution's thickening. -/
abbrev topShortComplex (sol : Solution t f G c) : ShortComplex sol.space.Modules :=
  ShortComplex.mk (RingedSpace.Hom.kernelIdealι sol.i)
    (SheafOfModules.unitToPushforwardObjUnit (RingedSpace.Hom.toRingCatSheafHom sol.i))
    (CategoryTheory.Limits.kernelSubobject_arrow_comp
      (SheafOfModules.RingedSite.KernelIdeal.map
        (RingedSpace.Hom.commRingSheafPushforwardMap sol.i)))

/-- The top kernel short complex of a solution is short exact. -/
theorem topShortComplex_shortExact (sol : Solution t f G c) :
    (topShortComplex sol).ShortExact := sorry

/-- The morphism of bundled thickenings determined by the maps `f` and `f'`. -/
def toArrowHom (sol : Solution t f G c) :
    MorphismProperty.Arrow.mk sol.i sol.i_isFirstOrder.toIsThickening ⟶
      Thickening.of t :=
  homMk f sol.f' sol.commutes.symm

/-- The two component squares of the filled short-complex diagram commute. -/
theorem toHom_comm (sol : Solution t f G c) :
    ((RingedSpace.Hom.pullbackPushforwardAdjunction sol.f').homEquiv
        (RingedSpace.Hom.kernelIdealSheaf t) (RingedSpace.Hom.kernelIdealSheaf sol.i)
        (Hom.idealMap (toArrowHom sol))) ≫
        ((topShortComplex sol).map (sol.f' _*)).f =
      (bottomShortComplex t).f ≫
        SheafOfModules.unitToPushforwardObjUnit
          (RingedSpace.Hom.toRingCatSheafHom sol.f') ∧
    SheafOfModules.unitToPushforwardObjUnit
          (RingedSpace.Hom.toRingCatSheafHom sol.f') ≫
        ((topShortComplex sol).map (sol.f' _*)).g =
      (bottomShortComplex t).g ≫
        ((t _*).map
            (SheafOfModules.unitToPushforwardObjUnit
              (RingedSpace.Hom.toRingCatSheafHom f)) ≫
          (RingedSpace.Hom.pushforwardCompIso f t).inv.app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (eqToIso
              (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pushforward h)
                sol.commutes.symm)).hom.app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (RingedSpace.Hom.pushforwardCompIso sol.i sol.f').hom.app
            (SheafOfModules.unit X.ringCatSheaf)) := sorry

/-- The filled diagram of a solution as a morphism of short complexes after pushforward. -/
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
  comm₁₂ := (toHom_comm sol).1
  comm₂₃ := (toHom_comm sol).2

/-- A solution satisfies the first-order, commutativity, and induced-kernel conditions. -/
theorem spec (sol : Solution t f G c) :
    IsFirstOrderThickening sol.i ∧
      sol.i ≫ sol.f' = f ≫ t ∧
        kernelMap sol ≫ (f _*).map sol.kernelIso.hom = c := sorry

/-- The kernel identification of a solution induces the prescribed map `c`. -/
theorem induces_c_eq (sol : Solution t f G c) :
    kernelMap sol ≫ (f _*).map sol.kernelIso.hom = c := sorry

end Solution

end AlgebraicGeometry.RingedSpace.Thickening
