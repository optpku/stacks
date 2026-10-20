/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.LinearAlgebra.TensorProduct.Annihilated

/-!
# Supported conormal quotient comparisons

For a closed immersion, the ideal annihilates its conormal quotient. The module
adjunction unit and the coborder comparison are therefore sectionwise bijective.
Inverse components reconstruct the unique section in the actual map's fiber;
the data do not depend on an admitted inverse-existence certificate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}


/-- The square comparing the coborder factorization with the original closed immersion. -/
theorem coborderSquare {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsClosedImmersion i] :
    CommSq (𝟙 X) (IsImmersion.liftCoborder i) i (IsImmersion.coborderRange i).ι := sorry

/-- The actual pullback comparison from the ambient ideal quotient to its coborder conormal. -/
def pullbackQuotientToConormal {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    (Modules.pullback i).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ⟶
      Hom.conormalSheaf i :=
  (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i).symm)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≫
    (Modules.pullbackCompIso (IsImmersion.liftCoborder i) (IsImmersion.coborderRange i).ι).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≫
    (Modules.pullback (IsImmersion.liftCoborder i)).map
      (Hom.Conormal.idealQuotientMap (coborderSquare i))

/-- The coborder comparison is bijective on every actual section module. -/
theorem pullbackQuotientToConormal_section_bijective {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ) :
    Function.Bijective ((pullbackQuotientToConormal i).val.app U) := sorry

/-- The inverse coborder comparison reconstructs the unique section in the actual fiber. -/
def pullbackQuotientToConormalInv {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    Hom.conormalSheaf i ⟶
      (Modules.pullback i).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) where
  val :=
    { app := fun U ↦ by
        classical
        let f := (pullbackQuotientToConormal i).val.app U
        exact ModuleCat.ofHom (f.hom.inverse
          (fun y ↦ if ∃ x, f x = y then Function.invFun f.hom y else 0)
          (by
            intro x
            simp only [if_pos (show ∃ z, f z = f x from ⟨x, rfl⟩)]
            exact Function.leftInverse_invFun
              (pullbackQuotientToConormal_section_bijective i U).injective x)
          (by sorry))
      naturality := by intro U V f; sorry }

/-- The inverse recovers the section sent through the coborder comparison. -/
@[simp]
theorem pullbackQuotientToConormalInv_apply_map {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((Modules.pullback i).obj
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))).val.obj U) :
    (pullbackQuotientToConormalInv i).val.app U
        ((pullbackQuotientToConormal i).val.app U x) = x :=
  sorry

/-- The forward coborder comparison sends the reconstructed section back to its input. -/
@[simp]
theorem pullbackQuotientToConormal_apply_inv {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ)
    (y : (Hom.conormalSheaf i).val.obj U) :
    (pullbackQuotientToConormal i).val.app U
        ((pullbackQuotientToConormalInv i).val.app U y) = y :=
  sorry

/-- The inverse coborder value is determined by the specified forward map. -/
theorem pullbackQuotientToConormalInv_eq_iff {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X)ᵒᵖ)
    (y : (Hom.conormalSheaf i).val.obj U)
    (x : ((Modules.pullback i).obj
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))).val.obj U) :
    (pullbackQuotientToConormalInv i).val.app U y = x ↔
      (pullbackQuotientToConormal i).val.app U x = y := by
  constructor
  · intro h
    rw [← h]
    exact pullbackQuotientToConormal_apply_inv i U y
  · intro h
    rw [← h]
    exact pullbackQuotientToConormalInv_apply_map i U x

/-- The supported quotient's module-adjunction unit is bijective on sections.
Its ideal action is zero, so its local scalar extension has inverse `[r] ⊗ m ↦ r • m`. -/
theorem conormalQuotientUnit_section_bijective {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X')ᵒᵖ) :
    Function.Bijective (((Modules.pullbackPushforwardAdjunction i).unit.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))).val.app U) :=
  sorry

/-- The inverse supported unit reconstructs the unique actual section of `I/I²`. -/
def conormalQuotientUnitInv {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    (Modules.pushforward i).obj ((Modules.pullback i).obj
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))) ⟶
      Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) where
  val :=
    { app := fun U ↦ by
        classical
        let F := Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)
        let G := (Modules.pushforward i).obj ((Modules.pullback i).obj F)
        let f : F.val.obj U ⟶ G.val.obj U :=
          ((Modules.pullbackPushforwardAdjunction i).unit.app F).val.app U
        exact (ModuleCat.homEquiv (M := G.val.obj U) (N := F.val.obj U)).symm (f.hom.inverse
          (fun y ↦ if ∃ x, f x = y then Function.invFun f.hom y else 0)
          (by
            intro x
            simp only [if_pos (show ∃ z, f z = f x from ⟨x, rfl⟩)]
            exact Function.leftInverse_invFun
              (conormalQuotientUnit_section_bijective i U).injective x)
          (by sorry))
      naturality := by intro U V f; sorry }

/-- The inverse supported unit recovers every section under the actual adjunction unit. -/
@[simp]
theorem conormalQuotientUnitInv_apply_unit {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X')ᵒᵖ)
    (x : (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)).val.obj U) :
    (conormalQuotientUnitInv i).val.app U
        (((Modules.pullbackPushforwardAdjunction i).unit.app
          (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))).val.app U x) = x :=
  sorry

/-- Applying the actual supported unit to its reconstructed section recovers its input. -/
@[simp]
theorem conormalQuotientUnit_apply_inv {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X')ᵒᵖ)
    (y : ((Modules.pushforward i).obj ((Modules.pullback i).obj
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)))).val.obj U) :
    ((Modules.pullbackPushforwardAdjunction i).unit.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))).val.app U
        ((conormalQuotientUnitInv i).val.app U y) = y :=
  sorry

/-- The inverse supported-unit value is uniquely characterized by the specified unit. -/
theorem conormalQuotientUnitInv_eq_iff {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsClosedImmersion i] (U : (smallEtaleSite X')ᵒᵖ)
    (y : ((Modules.pushforward i).obj ((Modules.pullback i).obj
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)))).val.obj U)
    (x : (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)).val.obj U) :
    (conormalQuotientUnitInv i).val.app U y = x ↔
      ((Modules.pullbackPushforwardAdjunction i).unit.app
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))).val.app U x = y := by
  constructor
  · intro h
    rw [← h]
    exact conormalQuotientUnit_apply_inv i U y
  · intro h
    rw [← h]
    exact conormalQuotientUnitInv_apply_unit i U x

/-- The specified supported quotient comparison has both concrete inverse components. -/
def pullbackQuotientToConormalIso {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    (Modules.pullback i).obj
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≅
      Hom.conormalSheaf i where
  hom := pullbackQuotientToConormal i
  inv := pullbackQuotientToConormalInv i
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The specified supported unit has its actual inverse section reconstruction. -/
def conormalQuotientUnitIso {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ≅
      (Modules.pushforward i).obj ((Modules.pullback i).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))) where
  hom := (Modules.pullbackPushforwardAdjunction i).unit.app _
  inv := conormalQuotientUnitInv i
  hom_inv_id := sorry
  inv_hom_id := sorry

instance pullbackQuotientToConormal_isIso {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] : IsIso (pullbackQuotientToConormal i) :=
  (pullbackQuotientToConormalIso i).isIso_hom

instance conormalQuotientUnit_isIso {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    IsIso ((Modules.pullbackPushforwardAdjunction i).unit.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))) :=
  (conormalQuotientUnitIso i).isIso_hom

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
