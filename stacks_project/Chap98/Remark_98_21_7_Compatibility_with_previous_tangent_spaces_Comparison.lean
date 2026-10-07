module

public import Mathlib.Algebra.Module.TransferInstance
public import stacks_project.Chap98.«98_8_0_1_TangentSpace»
public import stacks_project.Chap98.«98_8_0_2_InfinitesimalAut»
public import stacks_project.Chap98.Lemma_98_21_2_Functor

/-!
# Comparison of predeformation and RS* tangent spaces

For a locally Noetherian scheme `S`, a groupoid fibration `X` over `(Sch/S)_fppf`
satisfying (RS*), and a residue object `x0` over a finite-type field `k/S`, the
predeformation spaces `Tℱ_{X,k,x0}` and `Inf(ℱ_{X,k,x0})` are identified with
the RS* modules `T_{x0}(k)` and `Inf_{x0}(k)` by explicit `k`-linear equivalences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open TrivSqZeroExt

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)

/-- The ring map `k[ε] ⟶ k[k]` sending a dual number to the corresponding trivial
square-zero extension. -/
def dualNumberRingHom :
    (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier : Type u) →+*
      (trivSqZero (CommRingCat.of k) (ModuleCat.of k k) : Type u) :=
  { toFun x :=
      let y : DualNumber k := x
      ⟨(y.fst : k), (y.snd : k)⟩
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry }

/-- The ring equivalence of `k[ε]` with the trivial square-zero extension `k[k]`. -/
def dualNumberRingEquiv :
    (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier : Type u) ≃+*
      (trivSqZero (CommRingCat.of k) (ModuleCat.of k k) : Type u) :=
  RingEquiv.ofBijective (dualNumberRingHom) sorry

/-- The reverse ring map `k[k] ⟶ k[ε]`. -/
def dualNumberRingHom_symm :
    (trivSqZero (CommRingCat.of k) (ModuleCat.of k k) : Type u) →+*
      (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier : Type u) :=
  (dualNumberRingEquiv).symm.toRingHom

/-- The scheme morphism `Spec(k[ε]) ⟶ Spec(k[k])` induced by `dualNumberRingHom_symm`. -/
def specDualNumberLeftHom :
    Spec (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ⟶
      Spec (trivSqZero (CommRingCat.of k) (ModuleCat.of k k)) :=
  Spec.map <|
    @CommRingCat.ofHom
      (trivSqZero (CommRingCat.of k) (ModuleCat.of k k) : Type u)
      (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier : Type u)
      (CommRingCat.commRing _) (CommRingCat.commRing _)
      (dualNumberRingHom_symm)

/-- The scheme morphism `Spec(k[k]) ⟶ Spec(k[ε])` induced by `dualNumberRingHom`. -/
def specDualNumberLeftInv :
    Spec (trivSqZero (CommRingCat.of k) (ModuleCat.of k k)) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier) :=
  Spec.map <|
    @CommRingCat.ofHom
      (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier : Type u)
      (trivSqZero (CommRingCat.of k) (ModuleCat.of k k) : Type u)
      (CommRingCat.commRing _) (CommRingCat.commRing _)
      (dualNumberRingHom)

/-- The scheme isomorphism `Spec(k[ε]) ≅ Spec(k[k])` induced by `dualNumberRingHom`. -/
def specDualNumberLeftIso :
    Spec (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ≅
      Spec (trivSqZero (CommRingCat.of k) (ModuleCat.of k k)) where
  hom := specDualNumberLeftHom
  inv := specDualNumberLeftInv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `Spec(k[ε]) ⟶ S` through the affine open `Spec(Λ)` is isomorphic in `Over S` to
`Spec` of the trivial square-zero extension `k[k]`. -/
def specDualNumberIso
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    specDualNumber openImmersion k ≅
      Over.mk (specTrivSqZero kToS (ModuleCat.of k k)) :=
  Over.isoMk specDualNumberLeftIso
    (sorry : specDualNumberLeftIso.hom ≫ specTrivSqZero kToS (ModuleCat.of k k) =
      (specDualNumber openImmersion k).hom)

/-- The left component of `specDualNumberIso` is `Spec` of `dualNumberRingHom_symm`. -/
theorem specDualNumberIso_left :
    (specDualNumberIso openImmersion kToS h_factor).hom.left =
      Spec.map (CommRingCat.ofHom (dualNumberRingHom_symm)) := sorry

/-- `specDualNumberIso` followed by the canonical section `Spec(k[ε]) ⟶ Spec(k)` recovers
`specDualNumberToResidue`. -/
theorem specDualNumberIso_hom_comp :
    (specDualNumberIso openImmersion kToS h_factor).hom ≫
        specOverInl kToS (ModuleCat.of k k) =
      specDualNumberToResidue openImmersion k kToS h_factor := sorry

/-- The coefficient projection and `specDualNumberIso` recover `specOver_toResidue` of
`k[ε]`. -/
theorem specOverHom_comp_specDualNumberIso_inv :
    specOverHom (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
          (trivSqZeroHom_comp kToS (ModuleCat.of k k)) ≫
        (specDualNumberIso openImmersion kToS h_factor).inv =
      specOver_toResidue openImmersion kToS h_factor
        (ArtinianLocalAlgCat.dualNumber Λ k) := sorry

/-- `specOver_toResidue` of `k[ε]` followed by `specDualNumberIso` recovers the coefficient
projection in `Over S`. -/
theorem specOver_toResidue_comp_specDualNumberIso_hom :
    specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k) ≫
        (specDualNumberIso openImmersion kToS h_factor).hom =
      specOverHom (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
        (trivSqZeroHom_comp kToS (ModuleCat.of k k)) := sorry

variable (X : GroupoidsOver S)
variable (x0 : X.p.Fiber (Over.mk kToS))

/-- A dual-number fibre morphism remains a hom-lift after transporting the base arrow along
`specDualNumberIso`. -/
theorem dualNumberFiber_isHomLift
    (ξ : dualNumberFiber openImmersion kToS h_factor X x0) :
    X.p.IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
          (trivSqZeroHom_comp kToS (ModuleCat.of k k)) ≫
        (specDualNumberIso openImmersion kToS h_factor).inv)
      ξ.1.fromResidue := sorry

/-- A lift along `k[ε] ⟶ k` remains a hom-lift after transporting the base arrow along
`specDualNumberIso`. -/
theorem lift_isHomLift_specDualNumber
    (a : liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k))) :
    X.p.IsHomLift
      (specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k) ≫
        (specDualNumberIso openImmersion kToS h_factor).hom)
      a.hom := sorry

/-- Reindex the target of a dual-number fibre object along the identification
`ξ.base = k[ε]`. -/
def dualNumberFiber_target
    (ξ : dualNumberFiber openImmersion kToS h_factor X x0) :
    X.p.Fiber (specDualNumber openImmersion k) :=
  ⟨ξ.1.target.1, ξ.1.target.property.trans (congrArg (specOver openImmersion) ξ.property)⟩

/-- Send a dual-number fibre object to the corresponding lift along `k[ε] ⟶ k`. -/
def dualNumberFiberToLift
    (ξ : dualNumberFiber openImmersion kToS h_factor X x0) :
    liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k)) :=
  UnderLift.ofHom
    (specOverHom (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k)))
    x0
    (@Chosen.cartesianFactor _ _ _ _ X.p _
      (specDualNumber openImmersion k)
      (Over.mk (specTrivSqZero kToS (ModuleCat.of k k))) (Over.mk kToS)
      (specDualNumberIso openImmersion kToS h_factor).inv
      (specOverHom (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
        (trivSqZeroHom_comp kToS (ModuleCat.of k k)))
      (dualNumberFiber_target openImmersion kToS h_factor X x0 ξ)
      (Fiber.fiberInclusion.obj x0) ξ.1.fromResidue
      (dualNumberFiber_isHomLift openImmersion kToS h_factor X x0 ξ))

/-- Send a lift along `k[ε] ⟶ k` to the corresponding dual-number fibre object. -/
def liftToDualNumberFiber
    (a : liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k))) :
    dualNumberFiber openImmersion kToS h_factor X x0 :=
  ⟨Obj.of openImmersion kToS h_factor X x0 (ArtinianLocalAlgCat.dualNumber Λ k)
      (Chosen.reindexObj X.p (specDualNumberIso openImmersion kToS h_factor).hom a.codomain)
      (@Chosen.cartesianFactor _ _ _ _ X.p _
        (Over.mk (specTrivSqZero kToS (ModuleCat.of k k)))
        (specDualNumber openImmersion k) (Over.mk kToS)
        (specDualNumberIso openImmersion kToS h_factor).hom
        (specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k))
        a.codomain (Fiber.fiberInclusion.obj x0) a.hom
        (lift_isHomLift_specDualNumber openImmersion kToS h_factor X x0 a))
      (@Chosen.cartesianFactor.isHomLift _ _ _ _ X.p _
        (Over.mk (specTrivSqZero kToS (ModuleCat.of k k)))
        (specDualNumber openImmersion k) (Over.mk kToS)
        (specDualNumberIso openImmersion kToS h_factor).hom
        (specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k))
        a.codomain (Fiber.fiberInclusion.obj x0) a.hom
        (lift_isHomLift_specDualNumber openImmersion kToS h_factor X x0 a)),
    rfl⟩

/-- Objects of the dual-number fibre of `ℱ_{X,k,x0}` correspond to lifts of `x0` along
`k[ε] ⟶ k`. -/
def dualNumberFiberEquiv :
    dualNumberFiber openImmersion kToS h_factor X x0 ≃
      liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
        (trivSqZeroHom_comp kToS (ModuleCat.of k k)) where
  toFun := dualNumberFiberToLift openImmersion kToS h_factor X x0
  invFun := liftToDualNumberFiber openImmersion kToS h_factor X x0
  left_inv := sorry
  right_inv := sorry

/-- `dualNumberFiberEquiv` acts by `dualNumberFiberToLift`. -/
theorem dualNumberFiberEquiv_apply
    (ξ : dualNumberFiber openImmersion kToS h_factor X x0) :
    dualNumberFiberEquiv openImmersion kToS h_factor X x0 ξ =
      dualNumberFiberToLift openImmersion kToS h_factor X x0 ξ := sorry

/-- The reverse of `dualNumberFiberEquiv` acts by `liftToDualNumberFiber`. -/
theorem dualNumberFiberEquiv_symm_apply
    (a : liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k))) :
    (dualNumberFiberEquiv openImmersion kToS h_factor X x0).symm a =
      liftToDualNumberFiber openImmersion kToS h_factor X x0 a := sorry

variable [HasStrongRimSchlessinger X]

/-- Underlying type equivalence of `Tℱ_{X,k,x0}` with `T_{x0}(k)`. -/
def tangentSpaceTypeEquiv :
    tangentSpace openImmersion kToS h_factor X x0 ≃
      ((tangentFunctor x0).obj (ModuleCat.of k k) : Type (u + 1)) where
  toFun :=
    fun q ↦
      (tangentForget x0 (ModuleCat.of k k)).symm
        (Quotient.lift
          (fun ξ ↦ lifts.mk (dualNumberFiberEquiv openImmersion kToS h_factor X x0 ξ))
          (fun _ _ _ ↦ sorry) q)
  invFun :=
    fun t ↦
      Quotient.lift
        (fun a ↦ tangentSpace.mk openImmersion kToS h_factor X x0
          ((dualNumberFiberEquiv openImmersion kToS h_factor X x0).symm a))
        (fun _ _ _ ↦ sorry)
        (tangentForget x0 (ModuleCat.of k k) t)
  left_inv := sorry
  right_inv := sorry

/-- The additive group structure on `Tℱ_{X,k,x0}` transported from `T_{x0}(k)`. -/
instance instAddCommGroup_tangentSpace :
    AddCommGroup (tangentSpace openImmersion kToS h_factor X x0) :=
  Equiv.addCommGroup (tangentSpaceTypeEquiv openImmersion kToS h_factor X x0)

/-- The `k`-module structure on `Tℱ_{X,k,x0}` transported from `T_{x0}(k)`. -/
instance instModule_tangentSpace :
    Module k (tangentSpace openImmersion kToS h_factor X x0) :=
  Equiv.module k (tangentSpaceTypeEquiv openImmersion kToS h_factor X x0)

/-- Identification of `Tℱ_{X,k,x0}` with `T_{x0}(k)` as `k`-vector spaces. -/
def tangentSpaceEquiv :
    tangentSpace openImmersion kToS h_factor X x0 ≃ₗ[k]
      ((tangentFunctor x0).obj (ModuleCat.of k k) : Type (u + 1)) :=
  Equiv.linearEquiv k (tangentSpaceTypeEquiv openImmersion kToS h_factor X x0)

/-- `tangentSpaceEquiv` sends the class of a dual-number fibre object to the class of the
corresponding lift. -/
theorem tangentSpaceEquiv_mk
    (ξ : dualNumberFiber openImmersion kToS h_factor X x0) :
    tangentSpaceEquiv openImmersion kToS h_factor X x0
        (tangentSpace.mk openImmersion kToS h_factor X x0 ξ) =
      (tangentForget x0 (ModuleCat.of k k)).symm
        (lifts.mk (dualNumberFiberEquiv openImmersion kToS h_factor X x0 ξ)) :=
  sorry

/-- The reverse of `tangentSpaceEquiv` sends the class of a lift to the class of the
corresponding dual-number fibre object. -/
theorem tangentSpaceEquiv_symm_mk
    (a : liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k))) :
    (tangentSpaceEquiv openImmersion kToS h_factor X x0).symm
        ((tangentForget x0 (ModuleCat.of k k)).symm (lifts.mk a)) =
      tangentSpace.mk openImmersion kToS h_factor X x0
        ((dualNumberFiberEquiv openImmersion kToS h_factor X x0).symm a) :=
  sorry

/-- Chosen cartesian pullback of `x0` to `Spec(k[ε])`. -/
def dualNumberPullback :
    X.p.Fiber (specDualNumber openImmersion k) :=
  Chosen.reindexObj X.p
    (specDualNumberToResidue openImmersion k kToS h_factor) x0

/-- Selected cartesian arrow of the dual-number pullback of `x0`. -/
def dualNumberPullbackHom :
    Fiber.fiberInclusion.obj (dualNumberPullback openImmersion kToS h_factor X x0) ⟶
      Fiber.fiberInclusion.obj x0 :=
  Chosen.cartesianHom X.p
    (specDualNumberToResidue openImmersion k kToS h_factor) x0

/-- The selected dual-number pullback arrow is strongly cartesian. -/
instance dualNumberPullbackHom.isStronglyCartesian :
    X.p.IsStronglyCartesian
      (specDualNumberToResidue openImmersion k kToS h_factor)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0) :=
  Chosen.cartesianHom.isStronglyCartesian X.p
    (specDualNumberToResidue openImmersion k kToS h_factor) x0

/-- The dual-number pullback of `x0` is isomorphic to the reindexing of the trivial
deformation along `specDualNumberIso`. -/
def dualNumberPullbackIso :
    dualNumberPullback openImmersion kToS h_factor X x0 ≅
      Chosen.reindexObj X.p (specDualNumberIso openImmersion kToS h_factor).hom
        (trivialDeformation x0 (ModuleCat.of k k)) :=
  Chosen.Reindex.specifiedCompIsoApp X.p
    (specOverInl kToS (ModuleCat.of k k))
    (specDualNumberIso openImmersion kToS h_factor).hom
    (specDualNumberToResidue openImmersion k kToS h_factor)
    (specDualNumberIso_hom_comp openImmersion kToS h_factor) x0

/-- Composite comparison identifying iterated reindexing of the trivial deformation along
`specDualNumberIso` with the trivial deformation itself. -/
def trivialDeformationReindexIso :
    Chosen.reindexObj X.p (specDualNumberIso openImmersion kToS h_factor).inv
        (Chosen.reindexObj X.p (specDualNumberIso openImmersion kToS h_factor).hom
          (trivialDeformation x0 (ModuleCat.of k k))) ≅
      trivialDeformation x0 (ModuleCat.of k k) :=
  (Chosen.Reindex.specifiedCompIsoApp X.p
      (specDualNumberIso openImmersion kToS h_factor).hom
      (specDualNumberIso openImmersion kToS h_factor).inv
      (𝟙 (Over.mk (specTrivSqZero kToS (ModuleCat.of k k))))
      (specDualNumberIso openImmersion kToS h_factor).inv_hom_id
      (trivialDeformation x0 (ModuleCat.of k k))).symm.trans
    (Chosen.Reindex.eqId.isoApp X.p
      (𝟙 (Over.mk (specTrivSqZero kToS (ModuleCat.of k k)))) rfl
      (trivialDeformation x0 (ModuleCat.of k k)))

/-- Transport a fibre automorphism of the dual-number pullback to an automorphism of the
trivial deformation of `x0` to `k[ε]`. -/
def pullbackAutToTrivialAut
    (α : Aut (dualNumberPullback openImmersion kToS h_factor X x0)) :
    Aut (trivialDeformation x0 (ModuleCat.of k k)) :=
  let e := dualNumberPullbackIso openImmersion kToS h_factor X x0
  let c := trivialDeformationReindexIso openImmersion kToS h_factor X x0
  c.symm ≪≫
    (Chosen.reindex X.p (specDualNumberIso openImmersion kToS h_factor).inv).mapIso
      (e.symm ≪≫ α ≪≫ e) ≪≫
    c

/-- Transport an automorphism of the trivial deformation of `x0` to a fibre automorphism
of the dual-number pullback. -/
def trivialAutToPullbackAut
    (α : Aut (trivialDeformation x0 (ModuleCat.of k k))) :
    Aut (dualNumberPullback openImmersion kToS h_factor X x0) :=
  let e := dualNumberPullbackIso openImmersion kToS h_factor X x0
  e ≪≫
    (Chosen.reindex X.p (specDualNumberIso openImmersion kToS h_factor).hom).mapIso α ≪≫
    e.symm

/-- Underlying type equivalence of `Inf(ℱ_{X,k,x0})` with `Inf_{x0}(k)`. -/
def infinitesimalAutTypeEquiv :
    (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) ≃
      ((infFunctor x0).obj (ModuleCat.of k k) : Type u) where
  toFun α :=
    ⟨pullbackAutToTrivialAut openImmersion kToS h_factor X x0 α.1, sorry⟩
  invFun β :=
    ⟨trivialAutToPullbackAut openImmersion kToS h_factor X x0 β.1, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The additive group structure on `Inf(ℱ_{X,k,x0})` transported from `Inf_{x0}(k)`. -/
instance instAddCommGroup_infinitesimalAut :
    AddCommGroup
      (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) :=
  Equiv.addCommGroup
    (infinitesimalAutTypeEquiv openImmersion kToS h_factor X x0)

/-- The `k`-module structure on `Inf(ℱ_{X,k,x0})` transported from `Inf_{x0}(k)`. -/
instance instModule_infinitesimalAut :
    Module k
      (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) :=
  Equiv.module k
    (infinitesimalAutTypeEquiv openImmersion kToS h_factor X x0)

/-- Identification of `Inf(ℱ_{X,k,x0})` with `Inf_{x0}(k)` as `k`-vector spaces. -/
def infinitesimalAutEquiv :
    (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) ≃ₗ[k]
      ((infFunctor x0).obj (ModuleCat.of k k) : Type u) :=
  Equiv.linearEquiv k
    (infinitesimalAutTypeEquiv openImmersion kToS h_factor X x0)

/-- `infinitesimalAutEquiv` acts by transporting the underlying automorphism along the
pullback comparison with the trivial deformation. -/
theorem infinitesimalAutEquiv_apply
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    (infinitesimalAutEquiv openImmersion kToS h_factor X x0 α).1 =
      pullbackAutToTrivialAut openImmersion kToS h_factor X x0 α.1 :=
  sorry

/-- `infinitesimalAutEquiv` identifies the subgroup multiplication of
`Inf(ℱ_{X,k,x0})` with addition in `Inf_{x0}(k)`. -/
theorem infinitesimalAutEquiv_mul
    (α β : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    infinitesimalAutEquiv openImmersion kToS h_factor X x0 (α * β) =
      infinitesimalAutEquiv openImmersion kToS h_factor X x0 α +
        infinitesimalAutEquiv openImmersion kToS h_factor X x0 β :=
  sorry

/-- The image of a fibre automorphism under `infinitesimalAutEquiv` satisfies the
equalizer condition defining `infType`. -/
theorem infinitesimalAutEquiv_mem
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    (infinitesimalAutEquiv openImmersion kToS h_factor X x0 α).1.hom.1 ≫
        Chosen.cartesianHom X.p (specOverInl kToS (ModuleCat.of k k)) x0 =
      Chosen.cartesianHom X.p (specOverInl kToS (ModuleCat.of k k)) x0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
