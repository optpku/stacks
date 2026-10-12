/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Lemma_76_21_4_Homology
public import stacks_project.Chap91.Lemma_91_14_2
public import stacks_project.Chap93.Lemma_93_11_3_Trivial

/-!
# Ext/Hom/Der comparison maps for `Inf(Def_X)` and `T Def_X`

The identifications
`Inf(Def_X) ≃ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≃ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≃ Der_k(𝒪_X, 𝒪_X)`
and `T Def_X ≃ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` are realized by named comparison maps
assembled from Lemma 91.14.2, Lemma 76.21.4, and Definition 76.7.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor Limits
open Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Thickening
open AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
open ArtinianLocalAlgCat
open TrivSqZeroExt
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraicSpaceCat

variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/-- The structure morphism of `ofResidue X`, pinned as a map into `Spec k`. -/
def structureHomX : (ofResidue Λ k X).space ⟶ specObj (residue Λ k) :=
  (ofResidue Λ k X).structureHom

/-- `structureHomX` is the structure morphism of `ofResidue X`. -/
theorem structureHomX_eq :
    (structureHomX Λ k X) = (ofResidue Λ k X).structureHom :=
  sorry

/-- `structureHomX` is flat. -/
instance instFlat_structureHomX :
    AlgebraicSpace.Flat (structureHomX Λ k X) :=
  (ofResidue Λ k X).isFlat

/-- The closed immersion `Spec k ⟶ Spec k[ε]`. -/
abbrev dualNumberThickening : specObj (residue Λ k) ⟶ specObj (dualNumber Λ k) :=
  specMap (dualNumberToResidue Λ k)

/-- `dualNumberThickening` is the spectrum of the coefficient projection `k[ε] ⟶ k`. -/
theorem dualNumberThickening_eq :
    dualNumberThickening Λ k = specMap (dualNumberToResidue Λ k) :=
  sorry

/-- The dual-number closed immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_dualNumberToResidue :
    IsFirstOrderThickening (specMap (dualNumberToResidue Λ k)) :=
  sorry

/-- The trivial dual-number lift of the structure morphism as a flat first-order thickening lift. -/
def trivialFlatLift :
    FlatLift (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X) :=
  FlatLift.of (trivialSpaceOver Λ k X) (trivialSpaceImmersion Λ k X) sorry

/-- `trivialFlatLift` has ambient algebraic space `trivialSpace`. -/
theorem trivialFlatLift_space :
    (trivialFlatLift Λ k X).space = trivialSpace Λ k X :=
  sorry

/-- The kernel of the coefficient projection `k[ε] ⟶ k`, as a `k`-module. -/
abbrev dualNumberKernel :=
  LinearMap.ker (AlgHom.toLinearMap (fstHom k k k))

/-- An element of `ker(k[ε] → k)` is a dual number with vanishing scalar coefficient. -/
theorem mem_dualNumberKernel_iff (x : DualNumber k) :
    x ∈ dualNumberKernel k ↔ x.fst = 0 :=
  sorry

/-- `a·ε` lies in `ker(k[ε] → k)`. -/
theorem inr_mem_dualNumberKernel (a : k) :
    inr a ∈ dualNumberKernel k :=
  sorry

/-- ε-coefficient identification `ker(k[ε] → k) ≃ k`, sending `a·ε` to `a`. -/
def dualNumberKernelEquiv : dualNumberKernel k ≃ₗ[k] k where
  toFun x := snd (x : DualNumber k)
  invFun a := ⟨inr a, inr_mem_dualNumberKernel k a⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- `dualNumberKernelEquiv` is the second projection on a kernel element. -/
theorem dualNumberKernelEquiv_apply (x : dualNumberKernel k) :
    dualNumberKernelEquiv k x = snd (x : DualNumber k) :=
  sorry

/-- The inverse of `dualNumberKernelEquiv` sends `a` to `a·ε`. -/
theorem dualNumberKernelEquiv_symm_apply (a : k) :
    ((dualNumberKernelEquiv k).symm a : DualNumber k) = inr a :=
  sorry

/-- The identity object of the small étale site of `Spec k[ε]` over `Spec Λ`. -/
abbrev dualNumberEtaleId : smallEtaleSite (specObj (dualNumber Λ k)) :=
  smallEtaleSite.id (Over.mk (specHom (dualNumber Λ k)))

/-- The global section `ε` of `𝒪_{Spec k[ε]}`, as an element of the structure module
at the identity étale object. -/
def dualNumberEpsAtId :
    (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).val.obj
      (Opposite.op (dualNumberEtaleId Λ k)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).inv (inr (1 : k))

/-- The compatible family of sections of `𝒪_{Spec k[ε]}` obtained by restricting `ε`. -/
def dualNumberEpsSection :
    (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦
      (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).val.map
        (smallEtaleSite.homToId (Over.mk (specHom (dualNumber Λ k))) U.unop).op
        (dualNumberEpsAtId Λ k))
    sorry

/-- Multiplication by `ε` as an endomorphism of `𝒪_{Spec k[ε]}`. -/
def mulByEps :
    SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) ⟶
      SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) :=
  (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).unitHomEquiv.symm
    (dualNumberEpsSection Λ k)

/-- `mulByEps` sends the unit section to `ε`. -/
theorem mulByEps_apply :
    (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).unitHomEquiv
        (mulByEps Λ k) =
      dualNumberEpsSection Λ k :=
  sorry

/-- The sheaf morphism `𝒪_{Spec k[ε]} ⟶ ℐ` sending `1` to `ε`. -/
def epsToIdeal :
    SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) ⟶
      Hom.idealSheaf (specMap (dualNumberToResidue Λ k)) :=
  kernel.lift (Hom.idealSheafMap (specMap (dualNumberToResidue Λ k))) (mulByEps Λ k) sorry ≫
    (Hom.idealSheaf_spec (specMap (dualNumberToResidue Λ k))).inv

/-- `epsToIdeal` is the kernel lift of multiplication by `ε`. -/
theorem epsToIdeal_comp_ι :
    epsToIdeal Λ k ≫ Hom.idealSheafι (specMap (dualNumberToResidue Λ k)) = mulByEps Λ k :=
  sorry

/-- The carrier of `t_* 𝒪_{Spec k}` at the identity étale object of `Spec k[ε]`
identifies with `Γ(Spec k, ⊤)`. -/
theorem pushforwardUnit_obj_id :
    (((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).val.obj
      (Opposite.op (dualNumberEtaleId Λ k)) : Type _) =
      (Γ(Spec (CommRingCat.of (residue Λ k).carrier), ⊤) : Type _) :=
  sorry

/-- Identity-object ε-coefficient map on `Ker(𝒪_{Spec k[ε]} → t_* 𝒪_{Spec k})`,
sending `a·ε` to `a` via `dualNumberKernelEquiv` / `snd`. -/
def residueKernelToPushforwardAtId :
    (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))).val.obj
      (Opposite.op (dualNumberEtaleId Λ k)) ⟶
      ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).val.obj
        (Opposite.op (dualNumberEtaleId Λ k)) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun x ↦
          eqToHom (pushforwardUnit_obj_id Λ k).symm
            ((Scheme.ΓSpecIso (CommRingCat.of (residue Λ k).carrier)).inv
              (dualNumberKernelEquiv k
                ⟨(Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).hom
                    ((Hom.idealSheafι (specMap (dualNumberToResidue Λ k))).val.app
                      (Opposite.op (dualNumberEtaleId Λ k)) x),
                  sorry⟩)))
        sorry))
    sorry

/-- The global unit section of `t_* 𝒪_{Spec k}` at the identity étale object. -/
def residuePushforwardUnitAtId :
    ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).val.obj
      (Opposite.op (dualNumberEtaleId Λ k)) :=
  eqToHom (pushforwardUnit_obj_id Λ k).symm
    ((Scheme.ΓSpecIso (CommRingCat.of (residue Λ k).carrier)).inv 1)

/-- `residuePushforwardUnitAtId` is the global unit `1` of `𝒪_{Spec k}`. -/
theorem residuePushforwardUnitAtId_eq :
    residuePushforwardUnitAtId Λ k =
      eqToHom (pushforwardUnit_obj_id Λ k).symm
        ((Scheme.ΓSpecIso (CommRingCat.of (residue Λ k).carrier)).inv 1) :=
  sorry

/-- The compatible family of unit sections of `t_* 𝒪_{Spec k}` obtained by restricting
`1` along `smallEtaleSite.homToId`, as in `dualNumberEpsSection`. -/
def residuePushforwardUnitSection :
    ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦
      ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
          (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).val.map
        (smallEtaleSite.homToId (Over.mk (specHom (dualNumber Λ k))) U.unop).op
        (residuePushforwardUnitAtId Λ k))
    sorry

/-- `residuePushforwardUnitSection` restricts the identity-object unit along `homToId`. -/
theorem residuePushforwardUnitSection_apply
    (U : (smallEtaleSite (specObj (dualNumber Λ k)))ᵒᵖ) :
    (residuePushforwardUnitSection Λ k).val U =
      ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
          (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).val.map
        (smallEtaleSite.homToId (Over.mk (specHom (dualNumber Λ k))) U.unop).op
        (residuePushforwardUnitAtId Λ k) :=
  sorry

/-- The structure map `𝒪_{Spec k[ε]} ⟶ t_* 𝒪_{Spec k}` sending `1` to the
homToId-restriction of `1`. -/
def residueUnitToPushforward :
    SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) ⟶
      (Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k)))) :=
  ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
      (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).unitHomEquiv.symm
    (residuePushforwardUnitSection Λ k)

/-- `residueUnitToPushforward` is `unitHomEquiv` of the homToId-restricted unit section. -/
theorem residueUnitToPushforward_eq :
    residueUnitToPushforward Λ k =
      ((Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
          (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).unitHomEquiv.symm
        (residuePushforwardUnitSection Λ k) :=
  sorry

/-- Multiplication by `ε` is an epimorphism onto the kernel ideal. -/
instance instEpi_epsToIdeal : Epi (epsToIdeal Λ k) :=
  sorry

/-- ε-coefficient sheaf map `ℐ_{Spec k / Spec k[ε]} ⟶ t_* 𝒪_{Spec k}`, the unique
`𝒪_{Spec k[ε]}`-linear factorization of `residueUnitToPushforward` through
`epsToIdeal`. Its component on every étale chart is the projection `a·ε ↦ a`
sending the homToId-restriction of `ε` to the homToId-restriction of `1`. -/
def residueKernelToPushforward :
    Hom.idealSheaf (specMap (dualNumberToResidue Λ k)) ⟶
      (Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k)))) :=
  CategoryTheory.Abelian.epiDesc (epsToIdeal Λ k) (residueUnitToPushforward Λ k) sorry

/-- `residueKernelToPushforward` is characterized by sending `ε` to `1`. -/
theorem residueKernelToPushforward_comp_eps :
    epsToIdeal Λ k ≫ residueKernelToPushforward Λ k =
      residueUnitToPushforward Λ k :=
  sorry

/-- The identity-object component of `residueKernelToPushforward` is
`dualNumberKernelEquiv` / `snd`. -/
theorem residueKernelToPushforward_app_id :
    (residueKernelToPushforward Λ k).val.app (Opposite.op (dualNumberEtaleId Λ k)) =
      residueKernelToPushforwardAtId Λ k :=
  sorry

/-- ε-coefficient projection `t^* ℐ_{Spec k / Spec k[ε]} ⟶ 𝒪_{Spec k}`, the adjunct
of `residueKernelToPushforward`. -/
def residueKernelToUnit :
    (Modules.pullback (specMap (dualNumberToResidue Λ k))).obj
        (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ⟶
      SheafOfModules.unit (structureSheaf (specObj (residue Λ k))) :=
  ((Modules.pullbackPushforwardAdjunction
      (specMap (dualNumberToResidue Λ k))).homEquiv
      (Hom.idealSheaf (specMap (dualNumberToResidue Λ k)))
      (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).symm
    (residueKernelToPushforward Λ k)

/-- `residueKernelToUnit` is the adjunct of `residueKernelToPushforward`. -/
theorem residueKernelToUnit_eq :
    residueKernelToUnit Λ k =
      ((Modules.pullbackPushforwardAdjunction
          (specMap (dualNumberToResidue Λ k))).homEquiv
          (Hom.idealSheaf (specMap (dualNumberToResidue Λ k)))
          (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).symm
        (residueKernelToPushforward Λ k) :=
  sorry

/-- Inverse ε-coefficient map `𝒪_{Spec k} ⟶ t^* ℐ`, sending `a` to `a·ε`. -/
def residueUnitToKernel :
    SheafOfModules.unit (structureSheaf (specObj (residue Λ k))) ⟶
      (Modules.pullback (specMap (dualNumberToResidue Λ k))).obj
        (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) :=
  Modules.structureModulePullbackInv (specMap (dualNumberToResidue Λ k)) ≫
    (Modules.pullback (specMap (dualNumberToResidue Λ k))).map (epsToIdeal Λ k)

/-- ε-coefficient isomorphism `t^* ℐ_{Spec k / Spec k[ε]} ≅ 𝒪_{Spec k}`. -/
def residueKernelIsoUnit :
    (Modules.pullback (specMap (dualNumberToResidue Λ k))).obj
        (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ≅
      SheafOfModules.unit (structureSheaf (specObj (residue Λ k))) where
  hom := residueKernelToUnit Λ k
  inv := residueUnitToKernel Λ k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `residueKernelIsoUnit` is the ε-coefficient projection
`a·ε ↦ a`. -/
theorem residueKernelIsoUnit_hom :
    (residueKernelIsoUnit Λ k).hom = residueKernelToUnit Λ k :=
  sorry

/-- The inverse map of `residueKernelIsoUnit` is pullback of the map `1 ↦ ε`. -/
theorem residueKernelIsoUnit_inv :
    (residueKernelIsoUnit Λ k).inv = residueUnitToKernel Λ k :=
  sorry

/-- Identification `f^* 𝒞_{Spec k / Spec k[ε]} ≅ 𝒪_X` for the trivial dual-number
thickening, via the ε-coefficient isomorphism `ker(k[ε] → k) ≅ k`. -/
def pulledConormalUnitIso :
    pulledConormal (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X) ≅
      SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space) :=
  (Modules.pullback ((structureHomX Λ k X) ≫ specMap (dualNumberToResidue Λ k))).mapIso
      (conormalToIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
    (Modules.pullbackComp (structureHomX Λ k X)
        (specMap (dualNumberToResidue Λ k))).symm.app
      (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ≪≫
    (Modules.pullback (structureHomX Λ k X)).mapIso (residueKernelIsoUnit Λ k) ≪≫
    (Modules.structureModulePullbackIso (structureHomX Λ k X)).symm

/-- The forward map of `pulledConormalUnitIso` is pullback of the ε-coefficient iso. -/
theorem pulledConormalUnitIso_hom :
    (pulledConormalUnitIso Λ k X).hom =
      ((Modules.pullback
            ((structureHomX Λ k X) ≫ specMap (dualNumberToResidue Λ k))).mapIso
          (conormalToIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
        (Modules.pullbackComp (structureHomX Λ k X)
            (specMap (dualNumberToResidue Λ k))).symm.app
          (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ≪≫
        (Modules.pullback (structureHomX Λ k X)).mapIso (residueKernelIsoUnit Λ k) ≪≫
        (Modules.structureModulePullbackIso (structureHomX Λ k X)).symm).hom :=
  sorry

/-- The inverse map of `pulledConormalUnitIso` is pullback of the map `a ↦ a·ε`. -/
theorem pulledConormalUnitIso_inv :
    (pulledConormalUnitIso Λ k X).inv =
      ((Modules.pullback
            ((structureHomX Λ k X) ≫ specMap (dualNumberToResidue Λ k))).mapIso
          (conormalToIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
        (Modules.pullbackComp (structureHomX Λ k X)
            (specMap (dualNumberToResidue Λ k))).symm.app
          (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ≪≫
        (Modules.pullback (structureHomX Λ k X)).mapIso (residueKernelIsoUnit Λ k) ≪≫
        (Modules.structureModulePullbackIso (structureHomX Λ k X)).symm).inv :=
  sorry

/-- Ext⁰ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extZero :=
  Ext⁽(0 : ℤ)⁾((DerivedCategory.Q).obj NL[(structureHomX Λ k X)],
    (DerivedCategory.Q).obj
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).obj
        (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))))

/-- Ext¹ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extOne :=
  Ext⁽(1 : ℤ)⁾((DerivedCategory.Q).obj NL[(structureHomX Λ k X)],
    (DerivedCategory.Q).obj
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).obj
        (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))))

/-- Morphisms `Ω_{X/k} ⟶ 𝒪_X`. -/
abbrev homOmega :=
  Ω[(structureHomX Λ k X)] ⟶
    SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space)

/-- Derivations `Der_k(𝒪_X, 𝒪_X)`. -/
abbrev derivations :=
  Hom.derivations (structureHomX Λ k X)
    (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))

/-- Transport of an Ext class along `pulledConormalUnitIso`, in degree `n`. -/
def extNLMap (n : ℤ) {F G : Modules (ofResidue Λ k X).space} (φ : F ⟶ G) :
    Ext⁽n⁾((DerivedCategory.Q).obj NL[(structureHomX Λ k X)],
        (DerivedCategory.Q).obj
          ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).obj F)) →
      Ext⁽n⁾((DerivedCategory.Q).obj NL[(structureHomX Λ k X)],
        (DerivedCategory.Q).obj
          ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).obj G)) :=
  fun ξ ↦ ξ ≫ (shiftFunctor (DerivedCategory (Modules (ofResidue Λ k X).space)) n).map
    ((DerivedCategory.Q).map
      ((CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).map φ))

/-- Transport Ext⁰ of `f^* 𝒞` to Ext⁰ of `𝒪_X`. -/
def extZeroOfNL
    (ξ : extZeroNL (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X)) :
    extZero Λ k X :=
  extNLMap Λ k X (0 : ℤ) (pulledConormalUnitIso Λ k X).hom ξ

/-- Transport Ext⁰ of `𝒪_X` to Ext⁰ of `f^* 𝒞`. -/
def extZeroNLOf (ξ : extZero Λ k X) :
    extZeroNL (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X) :=
  extNLMap Λ k X (0 : ℤ) (pulledConormalUnitIso Λ k X).inv ξ

/-- Transport Ext¹ of `𝒪_X` to Ext¹ of `f^* 𝒞`. -/
def extOneNLOf (ξ : extOne Λ k X) :
    extOneNL (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X) :=
  extNLMap Λ k X (1 : ℤ) (pulledConormalUnitIso Λ k X).inv ξ

/-- The algebraic-space automorphism of `X'` underlying an infinitesimal automorphism of `X`. -/
def infSpaceHom (α : inf Λ k X) :
    trivialSpace Λ k X ⟶ trivialSpace Λ k X :=
  (fiberInclusion.map α.val.hom).spaceHom

/-- Automorphisms of the trivial lift reducing to the identity on `X`, from `Inf(Def_X)`. -/
def infToReduceIdAuto (α : inf Λ k X) : ReduceIdAuto (trivialFlatLift Λ k X) where
  hom := infSpaceHom Λ k X α
  over := sorry
  restrict := sorry
  isIso := sorry

/-- `infToReduceIdAuto` records the underlying algebraic-space automorphism of `α`. -/
theorem infToReduceIdAuto_apply (α : inf Λ k X) :
    (infToReduceIdAuto Λ k X α).hom = infSpaceHom Λ k X α :=
  sorry

/-- The comparison `Inf(Def_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`. -/
def infToExtZero : inf Λ k X → extZero Λ k X :=
  fun α ↦ extZeroOfNL Λ k X
    (reduceIdAutoEquiv (trivialFlatLift Λ k X) (infToReduceIdAuto Λ k X α))

/-- `infToExtZero` is `reduceIdAutoEquiv` of `infToReduceIdAuto`, transported to `𝒪_X`. -/
theorem infToExtZero_apply (α : inf Λ k X) :
    infToExtZero Λ k X α =
      extZeroOfNL Λ k X
        (reduceIdAutoEquiv (trivialFlatLift Λ k X) (infToReduceIdAuto Λ k X α)) :=
  sorry

/-- The comparison `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`,
assembled from `homologyZeroIso` and the degree-zero Hom/Ext chart. -/
def extZeroToHomOmegaOfUnit (ξ : extZero Λ k X) : homOmega Λ k X :=
  (homologyZeroIso (structureHomX Λ k X)).inv ≫
    (DerivedCategory.homologyFunctorFactors (Modules (ofResidue Λ k X).space) (0 : ℤ)).inv.app
      NL[(structureHomX Λ k X)] ≫
    (DerivedCategory.homologyFunctor (Modules (ofResidue Λ k X).space) (0 : ℤ)).map
      ((CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Modules (ofResidue Λ k X).space) (0 : ℤ)).hom.app
      (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))

/-- The comparison `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`,
via the canonical augmentation of `NL_{X/k}` and the degree-zero Ext chart. -/
def homOmegaToExtZeroOfUnit (α : homOmega Λ k X) : extZero Λ k X :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
    ((DerivedCategory.Q).map
      (augmentation (structureHomX Λ k X) ≫
        (CochainComplex.singleFunctor (Modules (ofResidue Λ k X).space) 0).map α) ≫
      (DerivedCategory.singleFunctorIsoCompQ (Modules (ofResidue Λ k X).space) (0 : ℤ)).hom.app
        (SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space)))

/-- The comparison `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≃ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`. -/
def extZeroEquivHomOmega : extZero Λ k X ≃ homOmega Λ k X where
  toFun ξ := extZeroToHomOmegaOfUnit Λ k X ξ
  invFun α := homOmegaToExtZeroOfUnit Λ k X α
  left_inv := sorry
  right_inv := sorry

/-- `extZeroEquivHomOmega` sends an Ext⁰ class to the corresponding map out of `Ω_{X/k}`. -/
theorem extZeroEquivHomOmega_apply (ξ : extZero Λ k X) :
    extZeroEquivHomOmega Λ k X ξ = extZeroToHomOmegaOfUnit Λ k X ξ :=
  sorry

/-- The comparison `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ⟶ Der_k(𝒪_X, 𝒪_X)`. -/
def homOmegaToDer (α : homOmega Λ k X) : derivations Λ k X :=
  (universalDerivation (structureHomX Λ k X)).postcomp
    ((SheafOfModules.forget (structureSheaf (ofResidue Λ k X).space) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (structureSheaf (ofResidue Λ k X).space).obj)).map α)

/-- The comparison `Der_k(𝒪_X, 𝒪_X) ⟶ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`, by descent of the
universal derivation. -/
def derToHomOmega (D : derivations Λ k X) : homOmega Λ k X :=
  (PresheafOfModules.sheafificationHomEquiv
      (α := 𝟙 (structureSheaf (ofResidue Λ k X).space).obj)
      (P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
        (commInverseImageStructureSheafMap (structureHomX Λ k X)).hom)
      (F := SheafOfModules.unit (structureSheaf (ofResidue Λ k X).space))).symm
    ((PresheafOfModules.DifferentialsConstruction.isUniversal'
        (commInverseImageStructureSheafMap (structureHomX Λ k X)).hom).desc D)

/-- The comparison `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≃ Der_k(𝒪_X, 𝒪_X)`. -/
def homOmegaEquivDer : homOmega Λ k X ≃ derivations Λ k X where
  toFun := homOmegaToDer Λ k X
  invFun := derToHomOmega Λ k X
  left_inv := sorry
  right_inv := sorry

/-- `homOmegaEquivDer` is postcomposition with the universal derivation. -/
theorem homOmegaEquivDer_apply (α : homOmega Λ k X) :
    homOmegaEquivDer Λ k X α = homOmegaToDer Λ k X α :=
  sorry

/-- The dual-number fibre object of `Def_X` associated to a flat first-order lift. -/
def ofFlatLift
    (L : FlatLift (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X)) :
    (deformationForget Λ k X).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X).obj
        (Over.mk
          (FlatAlgebraicSpaceCat.Hom.of (dualNumberToResidue Λ k) L.i L.isPullback.flip :
            FlatAlgebraicSpaceCat.of (dualNumber Λ k) L.space L.f' L.flat ⟶
              fiberInclusion.obj (residueObj Λ k X))) =
      dualNumber Λ k)

/-- Isomorphism classes of flat lifts map to tangent vectors of `Def_X`. -/
def ofIsoClass :
    IsoClass (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X) →
      tangentSpace Λ k X :=
  Quotient.lift (fun L ↦ tangentSpaceMk Λ k X (ofFlatLift Λ k X L)) sorry

/-- The class of a lift is sent to the class of `ofFlatLift`. -/
theorem ofIsoClass_mk
    (L : FlatLift (specMap (dualNumberToResidue Λ k)) (structureHomX Λ k X)) :
    ofIsoClass Λ k X (isoClassMk L) =
      tangentSpaceMk Λ k X (ofFlatLift Λ k X L) :=
  sorry

/-- The comparison `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ T Def_X`. -/
def ofExtOne : extOne Λ k X → tangentSpace Λ k X :=
  fun ξ ↦ ofIsoClass Λ k X
    (isoClassEquiv (trivialFlatLift Λ k X) (extOneNLOf Λ k X ξ))

/-- `ofExtOne` sends an Ext¹ class to the translate of the trivial lift. -/
theorem ofExtOne_apply (ξ : extOne Λ k X) :
    ofExtOne Λ k X ξ =
      ofIsoClass Λ k X
        (isoClassEquiv (trivialFlatLift Λ k X) (extOneNLOf Λ k X ξ)) :=
  sorry

/-- The zero Ext¹ class is sent to the trivial tangent vector. -/
theorem ofExtOne_zero : ofExtOne Λ k X 0 = trivialTangent Λ k X :=
  sorry

end FlatAlgebraicSpaceCat
