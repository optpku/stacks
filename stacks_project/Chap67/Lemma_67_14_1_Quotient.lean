/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

/-!
# Quotients of modules by ideal sheaves on algebraic spaces

The quotient `F / I F` of an `𝒪_X`-module by the action of an ideal sheaf is the
cokernel of that action on the small étale site. Along a morphism `i : Z ⟶ X`,
the adjunction unit `F ⟶ i_* i^* F` factors uniquely through this cokernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

variable {S : Scheme.{u}}

/-- The underlying ring presheaf of `𝒪_X` agrees with the commutative presentation. -/
theorem structureSheaf_obj_eq_comm (X : AlgebraicSpace S) :
    (structureSheaf X).obj = (commRingedSite X).structureSheaf.obj :=
  sorry

/-- Recast an `𝒪_X`-module from the `RingCat` presentation to the commutative étale
presentation. -/
noncomputable def toComm {X : AlgebraicSpace S} (F : X.Modules) :
    RingedSite.ModuleCat.{u} (commRingedSite X) where
  val := F.val
  isSheaf := F.isSheaf

/-- Recast an `𝒪_X`-module from the commutative étale presentation to the `RingCat`
presentation. -/
noncomputable def ofComm {X : AlgebraicSpace S}
    (F : RingedSite.ModuleCat.{u} (commRingedSite X)) : X.Modules where
  val := F.val
  isSheaf := F.isSheaf

/-- The underlying presheaf of modules is unchanged by `toComm`. -/
theorem toComm_val {X : AlgebraicSpace S} (F : X.Modules) :
    (toComm F).val = F.val :=
  sorry

/-- The underlying presheaf of modules is unchanged by `ofComm`. -/
theorem ofComm_val {X : AlgebraicSpace S}
    (F : RingedSite.ModuleCat.{u} (commRingedSite X)) :
    (ofComm F).val = F.val :=
  sorry

/-- Recasting to the commutative presentation and back recovers the original module. -/
theorem ofComm_toComm {X : AlgebraicSpace S} (F : X.Modules) :
    ofComm (toComm F) = F :=
  sorry

/-- Recasting from the commutative presentation and back recovers the original module. -/
theorem toComm_ofComm {X : AlgebraicSpace S}
    (F : RingedSite.ModuleCat.{u} (commRingedSite X)) :
    toComm (ofComm F) = F :=
  sorry

/-- A morphism of `𝒪_X`-modules recast to the commutative étale presentation. -/
noncomputable def toCommMap {X : AlgebraicSpace S} {F G : X.Modules} (f : F ⟶ G) :
    toComm F ⟶ toComm G where
  val := f.val

/-- A morphism of commutative étale `𝒪_X`-modules recast to the `RingCat` presentation. -/
noncomputable def ofCommMap {X : AlgebraicSpace S}
    {F G : RingedSite.ModuleCat.{u} (commRingedSite X)} (f : F ⟶ G) :
    ofComm F ⟶ ofComm G where
  val := f.val

/-- The underlying presheaf morphism of `toCommMap` is the original morphism. -/
theorem toCommMap_val {X : AlgebraicSpace S} {F G : X.Modules} (f : F ⟶ G) :
    (toCommMap f).val = f.val :=
  sorry

/-- The underlying presheaf morphism of `ofCommMap` is the original morphism. -/
theorem ofCommMap_val {X : AlgebraicSpace S}
    {F G : RingedSite.ModuleCat.{u} (commRingedSite X)} (f : F ⟶ G) :
    (ofCommMap f).val = f.val :=
  sorry

/-- The structure module of `𝒪_X` recasts to the commutative tensor unit. -/
noncomputable def toCommUnitIso (X : AlgebraicSpace S) :
    toComm (SheafOfModules.unit (structureSheaf X)) ≅
      unitModule (smallEtaleTopology X) (commStructureSheaf X) where
  hom := { val := 𝟙 _ }
  inv := { val := 𝟙 _ }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The inclusion of an ideal sheaf, recast as a morphism into the commutative structure
module. -/
noncomputable def toCommArrow {X : AlgebraicSpace S} (I : IdealSubobject X) :
    toComm I.toModule ⟶ unitModule (smallEtaleTopology X) (commStructureSheaf X) :=
  toCommMap I.arrow ≫ (toCommUnitIso X).hom

/-- The recast ideal inclusion is a monomorphism. -/
instance toCommArrow_mono {X : AlgebraicSpace S} (I : IdealSubobject X) :
    Mono (toCommArrow I) :=
  sorry

/-- An ideal subobject of `𝒪_X`, recast as a subobject of the commutative structure module. -/
noncomputable def toCommSubobject {X : AlgebraicSpace S} (I : IdealSubobject X) :
    Subobject (unitModule (smallEtaleTopology X) (commStructureSheaf X)) :=
  Subobject.mk (toCommArrow I)

/-- `toCommSubobject` is the subobject represented by the recast ideal inclusion. -/
theorem toCommSubobject_eq_mk {X : AlgebraicSpace S} (I : IdealSubobject X) :
    toCommSubobject I = Subobject.mk (toCommArrow I) :=
  sorry

/-- The action `I ⊗ F ⟶ F` of an ideal sheaf on an `𝒪_X`-module. -/
noncomputable def idealAction {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : X.Modules) :
    ofComm
        (tensorObj
          (toCommSubobject I : RingedSite.ModuleCat.{u} (commRingedSite X))
          (toComm F)) ⟶
      F :=
  ofCommMap (IdealSheaf.action (toCommSubobject I) (toComm F))

/-- The action of an ideal sheaf is the recast of the commutative étale action. -/
theorem idealAction_eq {X : AlgebraicSpace S} (I : IdealSubobject X) (F : X.Modules) :
    idealAction I F =
      ofCommMap (IdealSheaf.action (toCommSubobject I) (toComm F)) :=
  sorry

/-- The quotient module `F / I F`, as the cokernel of the ideal-sheaf action. -/
noncomputable def quotientByIdeal {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : X.Modules) : X.Modules :=
  cokernel (idealAction I F)

/-- The canonical projection `F ⟶ F / I F`. -/
noncomputable def quotientByIdeal.π {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : X.Modules) : F ⟶ quotientByIdeal I F :=
  cokernel.π (idealAction I F)

/-- The projection `F ⟶ F / I F` is the cokernel projection of the ideal-sheaf action. -/
theorem quotientByIdeal.π_eq {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : X.Modules) :
    quotientByIdeal.π I F = cokernel.π (idealAction I F) :=
  sorry

/-- The ideal-sheaf action followed by the adjunction unit `F ⟶ i_* i^* F` is zero. -/
theorem idealAction_comp_unit {Z X : AlgebraicSpace S} (i : Z ⟶ X) (F : X.Modules) :
    idealAction (Hom.idealSheafSubobject i) F ≫
        (pullbackPushforwardAdjunction i).unit.app F =
      0 :=
  sorry

/-- The comparison `F / I F ⟶ i_* i^* F` induced by the module adjunction unit. -/
noncomputable def quotientByIdealComparison {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (F : X.Modules) :
    quotientByIdeal (Hom.idealSheafSubobject i) F ⟶
      (pushforward i).obj ((pullback i).obj F) :=
  cokernel.desc (idealAction (Hom.idealSheafSubobject i) F)
    ((pullbackPushforwardAdjunction i).unit.app F) (idealAction_comp_unit i F)

/-- The comparison morphism is the cokernel descent of the adjunction unit. -/
theorem quotientByIdealComparison_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (F : X.Modules) :
    quotientByIdealComparison i F =
      cokernel.desc (idealAction (Hom.idealSheafSubobject i) F)
        ((pullbackPushforwardAdjunction i).unit.app F) (idealAction_comp_unit i F) :=
  sorry

/-- The quotient projection followed by the comparison morphism is the adjunction unit. -/
theorem π_comp_comparison {Z X : AlgebraicSpace S} (i : Z ⟶ X) (F : X.Modules) :
    quotientByIdeal.π (Hom.idealSheafSubobject i) F ≫ quotientByIdealComparison i F =
      (pullbackPushforwardAdjunction i).unit.app F :=
  sorry

/-- The comparison morphism is the unique factorization of the adjunction unit through
`F / I F`. -/
theorem comparison_eq_unit {Z X : AlgebraicSpace S} (i : Z ⟶ X) (F : X.Modules)
    {g :
      quotientByIdeal (Hom.idealSheafSubobject i) F ⟶
        (pushforward i).obj ((pullback i).obj F)}
    (hg :
      quotientByIdeal.π (Hom.idealSheafSubobject i) F ≫ g =
        (pullbackPushforwardAdjunction i).unit.app F) :
    g = quotientByIdealComparison i F :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
