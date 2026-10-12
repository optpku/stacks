/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk

/-!
# Stalks of sheaves of modules

This file lifts the presheaf module-stalk API through `SheafOfModules.forget`, and provides the
commutative-ring and unit-module comparisons needed by ringed-space applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

/- The conventional notation for the canonical category of sheaves of modules. -/
notation:max "Mod(" 𝒪 ")" => SheafOfModules 𝒪

namespace SheafOfModules

variable {Z : TopCat.{u}}

/-- Taking the stalk of a sheaf of modules at `x` is a functor to modules over the stalk of the
ring sheaf. -/
noncomputable def stalkFunctor
    (𝒪 : Z.Sheaf RingCat.{u}) (x : Z) :
    SheafOfModules 𝒪 ⥤ ModuleCat (𝒪.presheaf.stalk x) :=
  SheafOfModules.forget 𝒪 ⋙
    PresheafOfModules.stalkFunctor 𝒪.presheaf x

/-- The germ at `x` of a global section of a sheaf of modules over a ring sheaf. -/
@[stacks 01AN "global-section germ"]
noncomputable abbrev sectionGerm
    {𝒪 : Z.Sheaf RingCat.{u}} {ℱ : SheafOfModules 𝒪}
    (s : ℱ.sections) (x : Z) : (stalkFunctor 𝒪 x).obj ℱ :=
  TopCat.Presheaf.Γgerm ℱ.val.presheaf x
    (s.1 (Opposite.op (⊤ : Opens Z)))

/-- Taking stalks of module sheaves over a ring sheaf is additive. -/
instance stalkFunctor_additive
    (𝒪 : Z.Sheaf RingCat.{u}) (x : Z) :
    (stalkFunctor 𝒪 x).Additive := sorry

/-- Taking stalks of module sheaves over a ring sheaf preserves all small colimits whenever
additive sheafification is available. -/
@[stacks 01AH "stalks preserve colimits", instance]
theorem stalkFunctor_preservesColimits
    (𝒪 : Z.Sheaf RingCat.{u}) (x : Z)
    [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesColimits (stalkFunctor 𝒪 x) := sorry

/-- The short complex of stalk modules obtained by taking the stalk at `x` of every term and
morphism of a short complex of module sheaves over `𝒪`. -/
noncomputable abbrev stalkShortComplex
    (𝒪 : Z.Sheaf RingCat.{u}) (S : ShortComplex (SheafOfModules 𝒪)) (x : Z) :
    ShortComplex (ModuleCat (𝒪.presheaf.stalk x)) :=
  S.map (stalkFunctor 𝒪 x)

/-- The stalk-module map of a morphism of module sheaves sends the germ of a section to the germ
of its sectionwise image. -/
theorem stalkFunctor_map_germ
    {𝒪 : Z.Sheaf RingCat.{u}} {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢)
    (U : Opens Z) (x : Z) (hx : x ∈ U) (m : ℱ.val.obj (Opposite.op U)) :
    ((stalkFunctor 𝒪 x).map f).hom
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx m) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hx
        (f.val.app (Opposite.op U) m) := sorry

end SheafOfModules

namespace TopCat.Sheaf

/-- The stalk of a module sheaf over the underlying ring sheaf of `𝒪` carries the canonical
module structure over the commutative-ring stalk `𝒪_x`. -/
noncomputable instance ringSheafOfCommStalkModule
    {Y : TopCat.{u}} {𝒪 : Y.Sheaf CommRingCat.{u}}
    (ℱ : SheafOfModules (ringSheafOfComm 𝒪)) (x : Y) :
    Module (𝒪.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ℱ.val x

end TopCat.Sheaf

namespace SheafOfModules

variable {Z : TopCat.{u}}

/-- Taking the stalk of a module sheaf over the underlying ring sheaf of a commutative-ring sheaf
is a functor to modules over the commutative-ring stalk. -/
noncomputable def stalkFunctorOfCommRing
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪) ⥤
      ModuleCat (𝒪.presheaf.stalk x) :=
  SheafOfModules.forget (TopCat.Sheaf.ringSheafOfComm 𝒪) ⋙
    PresheafOfModules.stalkFunctorOfCommRing 𝒪.presheaf x

/-- The germ at `x` of a global section of a module sheaf over a commutative-ring sheaf. -/
@[stacks 01AN "commutative global-section germ"]
noncomputable abbrev sectionGermOfCommRing
    {𝒪 : Z.Sheaf CommRingCat.{u}}
    {ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    (s : ℱ.sections) (x : Z) : (stalkFunctorOfCommRing 𝒪 x).obj ℱ :=
  TopCat.Presheaf.Γgerm ℱ.val.presheaf x
    (s.1 (Opposite.op (⊤ : Opens Z)))

/-- Taking stalks of module sheaves over an underlying commutative-ring sheaf is additive. -/
instance stalkFunctorOfCommRing_additive
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    (stalkFunctorOfCommRing 𝒪 x).Additive := sorry

/-- Taking stalks of module sheaves over a commutative-ring sheaf preserves all small colimits
whenever additive sheafification is available. -/
@[stacks 01AH "commutative-ring stalks preserve colimits", instance]
theorem stalkFunctorOfCommRing_preservesColimits
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z)
    [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesColimits (stalkFunctorOfCommRing 𝒪 x) := sorry

/-- The short complex of stalk modules obtained by taking the stalk at `x` of every term and
morphism of a short complex over the underlying ring sheaf of `𝒪`. -/
noncomputable abbrev stalkShortComplexOfCommRing
    (𝒪 : Z.Sheaf CommRingCat.{u})
    (S : ShortComplex (SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))) (x : Z) :
    ShortComplex (ModuleCat (𝒪.presheaf.stalk x)) :=
  S.map (stalkFunctorOfCommRing 𝒪 x)

/-- The commutative-ring stalk-module map of a morphism of module sheaves sends the germ of a
section to the germ of its sectionwise image. -/
theorem stalkFunctorOfCommRing_map_germ
    {𝒪 : Z.Sheaf CommRingCat.{u}}
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢)
    (U : Opens Z) (x : Z) (hx : x ∈ U) (m : ℱ.val.obj (Opposite.op U)) :
    ((stalkFunctorOfCommRing 𝒪 x).map f).hom
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx m) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hx
        (f.val.app (Opposite.op U) m) := sorry

/-- The canonical additive comparison from the stalk of the unit module sheaf of `𝒪` to the
underlying additive group of the ring stalk `𝒪ₓ`. -/
noncomputable abbrev unitStalkAddIso
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    TopCat.Presheaf.stalk
        (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf x ≅
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat).obj
        (𝒪.presheaf.stalk x) :=
  (preservesColimitIso
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ 𝒪.presheaf)).symm

/-- The forward function from the stalk of the unit module sheaf of `𝒪` to the ring stalk
`𝒪ₓ`. -/
noncomputable abbrev unitStalkToRingStalk
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    (stalkFunctorOfCommRing 𝒪 x).obj
        (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)) → 𝒪.presheaf.stalk x :=
  ConcreteCategory.hom (unitStalkAddIso 𝒪 x).hom

/-- The inverse function from the ring stalk `𝒪ₓ` to the stalk of the unit module sheaf of
`𝒪`. -/
noncomputable abbrev ringStalkToUnitStalk
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    𝒪.presheaf.stalk x →
      (stalkFunctorOfCommRing 𝒪 x).obj
        (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)) :=
  ConcreteCategory.hom (unitStalkAddIso 𝒪 x).inv

/-- The unit-stalk comparison preserves addition. -/
theorem unitStalkToRingStalk_add
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z)
    (m n : (stalkFunctorOfCommRing 𝒪 x).obj
      (unit (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    unitStalkToRingStalk 𝒪 x (m + n) =
      unitStalkToRingStalk 𝒪 x m + unitStalkToRingStalk 𝒪 x n := sorry

/-- The unit-stalk comparison is linear over the ring stalk `𝒪ₓ`. -/
theorem unitStalkToRingStalk_smul
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) (r : 𝒪.presheaf.stalk x)
    (m : (stalkFunctorOfCommRing 𝒪 x).obj
      (unit (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    unitStalkToRingStalk 𝒪 x (r • m) = r • unitStalkToRingStalk 𝒪 x m := sorry

/-- The inverse additive comparison is a left inverse of the unit-stalk comparison. -/
@[simp]
theorem ringStalkToUnitStalk_apply_unitStalkToRingStalk
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z)
    (m : (stalkFunctorOfCommRing 𝒪 x).obj
      (unit (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    ringStalkToUnitStalk 𝒪 x (unitStalkToRingStalk 𝒪 x m) = m := sorry

/-- The inverse additive comparison is a right inverse of the unit-stalk comparison. -/
@[simp]
theorem unitStalkToRingStalk_apply_ringStalkToUnitStalk
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) (r : 𝒪.presheaf.stalk x) :
    unitStalkToRingStalk 𝒪 x (ringStalkToUnitStalk 𝒪 x r) = r := sorry

/-- The canonical linear equivalence between the stalk of the unit module sheaf of `𝒪` and the
ring stalk `𝒪ₓ`. -/
noncomputable def unitStalkLinearEquiv
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    (stalkFunctorOfCommRing 𝒪 x).obj
        (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)) ≃ₗ[𝒪.presheaf.stalk x]
      𝒪.presheaf.stalk x where
  toFun := unitStalkToRingStalk 𝒪 x
  invFun := ringStalkToUnitStalk 𝒪 x
  left_inv := ringStalkToUnitStalk_apply_unitStalkToRingStalk 𝒪 x
  right_inv := unitStalkToRingStalk_apply_ringStalkToUnitStalk 𝒪 x
  map_add' := unitStalkToRingStalk_add 𝒪 x
  map_smul' := unitStalkToRingStalk_smul 𝒪 x

/-- The canonical linear map from the stalk of the unit module sheaf of `𝒪` to the ring stalk
`𝒪ₓ`. -/
noncomputable abbrev unitStalkLinearMap
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    (stalkFunctorOfCommRing 𝒪 x).obj
        (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)) ⟶
      ModuleCat.of (𝒪.presheaf.stalk x) (𝒪.presheaf.stalk x) :=
  ModuleCat.ofHom (unitStalkLinearEquiv 𝒪 x).toLinearMap

/-- The forward map of `unitStalkLinearEquiv` is the canonical additive comparison. -/
@[simp]
theorem unitStalkLinearEquiv_apply
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z)
    (m : (stalkFunctorOfCommRing 𝒪 x).obj
      (unit (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    unitStalkLinearEquiv 𝒪 x m = unitStalkToRingStalk 𝒪 x m := sorry

/-- The inverse map of `unitStalkLinearEquiv` is the inverse additive comparison. -/
@[simp]
theorem unitStalkLinearEquiv_symm_apply
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) (r : 𝒪.presheaf.stalk x) :
    (unitStalkLinearEquiv 𝒪 x).symm r = ringStalkToUnitStalk 𝒪 x r := sorry

/-- A section of the unit module sheaf of `𝒪`, viewed as a section of `𝒪`. -/
abbrev unitSectionToRingSection
    {𝒪 : Z.Sheaf CommRingCat.{u}} (U : Opens Z) :
    (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.obj (Opposite.op U) →
      𝒪.presheaf.obj (Opposite.op U) :=
  fun s => s

/-- The unit-stalk comparison sends the germ of a section of `𝒪` to the same germ in the ring
stalk. -/
theorem unitStalkToRingStalk_germ
    {𝒪 : Z.Sheaf CommRingCat.{u}} (x : Z) (U : Opens Z) (hx : x ∈ U)
    (s : 𝒪.presheaf.obj (Opposite.op U)) :
    unitStalkToRingStalk 𝒪 x
        (TopCat.Presheaf.germ
          (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf U x hx s) =
      𝒪.presheaf.germ U x hx s := sorry

/-- The canonical unit-stalk linear map sends a section germ to the corresponding ring germ. -/
theorem unitStalkLinearMap_germ
    {𝒪 : Z.Sheaf CommRingCat.{u}} (x : Z) (U : Opens Z) (hx : x ∈ U)
    (s : (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.obj (Opposite.op U)) :
    (unitStalkLinearMap 𝒪 x).hom
        (TopCat.Presheaf.germ
          (unit (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf U x hx s) =
      𝒪.presheaf.germ U x hx (unitSectionToRingSection U s) := sorry

end SheafOfModules
