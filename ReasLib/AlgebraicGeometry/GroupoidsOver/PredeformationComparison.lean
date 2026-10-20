module

public import Mathlib.Algebra.Module.TransferInstance
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.InfinitesimalAutomorphisms
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor

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

/-- `Spec(k[ε]) ⟶ S` through the affine open `Spec(Λ)` is isomorphic in `Over S` to
`Spec` of the trivial square-zero extension `k[k]`. -/
def specDualNumberIso
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    specDualNumber openImmersion k ≅
      Over.mk (specTrivSqZero kToS (ModuleCat.of k k)) := by
  refine Over.isoMk ?_ ?_
  · let e : (trivSqZero (CommRingCat.of k) (ModuleCat.of k k) : Type u) ≃+*
        ((ArtinianLocalAlgCat.dualNumber Λ k).carrier : Type u) :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := by
          intro a b
          apply TrivSqZeroExt.ext
          · rfl
          · change a.fst * b.snd + b.fst * a.snd = a.fst * b.snd + a.snd * b.fst
            rw [mul_comm b.fst a.snd]
        map_add' := fun _ _ ↦ rfl }
    exact Scheme.Spec.mapIso e.toCommRingCatIso.op
  · sorry

/-- `specDualNumberIso` followed by the canonical section `Spec(k[ε]) ⟶ Spec(k)` recovers
`specDualNumberToResidue`. -/
theorem specDualNumberIso_hom_comp :
    (specDualNumberIso openImmersion kToS h_factor).hom ≫
        specOverInl kToS (ModuleCat.of k k) =
      specDualNumberToResidue openImmersion k kToS h_factor := sorry

variable (X : GroupoidsOver S)
variable (x0 : X.p.Fiber (Over.mk kToS))

/-- Send a dual-number fibre object to the corresponding lift along `k[ε] ⟶ k`. -/
def dualNumberFiberToLift
    (ξ : ((predeformationFunctor X openImmersion kToS h_factor x0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k))) :
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
      ⟨ξ.1.target.1, ξ.1.target.property.trans
        (congrArg (specOver openImmersion) ξ.property)⟩
      (Fiber.fiberInclusion.obj x0) ξ.1.fromResidue
      (by sorry))

/-- Send a lift along `k[ε] ⟶ k` to the corresponding dual-number fibre object. -/
def liftToDualNumberFiber
    (a : liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k))) :
    ((predeformationFunctor X openImmersion kToS h_factor x0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) := by
  have homLift : X.p.IsHomLift
      (specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k) ≫
        (specDualNumberIso openImmersion kToS h_factor).hom) a.hom := sorry
  exact ⟨Obj.of openImmersion kToS h_factor X x0 (ArtinianLocalAlgCat.dualNumber Λ k)
      (Chosen.reindexObj X.p (specDualNumberIso openImmersion kToS h_factor).hom a.codomain)
      (@Chosen.cartesianFactor _ _ _ _ X.p _
        (Over.mk (specTrivSqZero kToS (ModuleCat.of k k)))
        (specDualNumber openImmersion k) (Over.mk kToS)
        (specDualNumberIso openImmersion kToS h_factor).hom
        (specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k))
        a.codomain (Fiber.fiberInclusion.obj x0) a.hom
        homLift)
      (@Chosen.cartesianFactor.isHomLift _ _ _ _ X.p _
        (Over.mk (specTrivSqZero kToS (ModuleCat.of k k)))
        (specDualNumber openImmersion k) (Over.mk kToS)
        (specDualNumberIso openImmersion kToS h_factor).hom
        (specOver_toResidue openImmersion kToS h_factor
          (ArtinianLocalAlgCat.dualNumber Λ k))
        a.codomain (Fiber.fiberInclusion.obj x0) a.hom
        homLift),
    rfl⟩

/-- Underlying type equivalence of `Tℱ_{X,k,x0}` with `T_{x0}(k)`. -/
def tangentSpaceTypeEquiv [hRS : HasStrongRimSchlessinger X] :
    (CategoryTheory.Functor.tangentSpace (predeformationFunctor X openImmersion kToS h_factor x0)) ≃
      ((tangentFunctor x0).obj (ModuleCat.of k k) : Type (u + 1)) := by
  let forward := fun ξ ↦ lifts.mk
    (dualNumberFiberToLift openImmersion kToS h_factor X x0 ξ)
  let backward := fun a ↦ CategoryTheory.Functor.tangentSpace.mk (predeformationFunctor X openImmersion kToS h_factor x0)
    (liftToDualNumberFiber openImmersion kToS h_factor X x0 a)
  have laws :
      (∀ ξ η, Nonempty (ξ ≅ η) → forward ξ = forward η) ∧
      (∀ a b, Nonempty (a ≅ b) → backward a = backward b) ∧
      (∀ (hf : ∀ ξ η, Nonempty (ξ ≅ η) → forward ξ = forward η)
        (hb : ∀ a b, Nonempty (a ≅ b) → backward a = backward b),
        Function.LeftInverse
          (fun t ↦ Quotient.lift backward hb (tangentForget x0 (ModuleCat.of k k) t))
          (fun q ↦ (tangentForget x0 (ModuleCat.of k k)).symm (Quotient.lift forward hf q)) ∧
        Function.RightInverse
          (fun t ↦ Quotient.lift backward hb (tangentForget x0 (ModuleCat.of k k) t))
          (fun q ↦ (tangentForget x0 (ModuleCat.of k k)).symm (Quotient.lift forward hf q))) := sorry
  exact
    { toFun := fun q ↦ (tangentForget x0 (ModuleCat.of k k)).symm
        (Quotient.lift forward laws.1 q)
      invFun := fun t ↦ Quotient.lift backward laws.2.1
        (tangentForget x0 (ModuleCat.of k k) t)
      left_inv := (laws.2.2 laws.1 laws.2.1).1
      right_inv := (laws.2.2 laws.1 laws.2.1).2 }

/-- Strong Rim-Schlessinger descent gives Schlessinger's (H2) for the
isomorphism-class functor of residue lifts. -/
instance instHasSchlessingerH2_fiberIsoClass_predeformationFunctor
    [hRS : HasStrongRimSchlessinger X] :
    HasSchlessingerH2 (fiberIsoClassFunctor
      (predeformationFunctor X openImmersion kToS h_factor x0)) := sorry

/-- The tangent quotient has its canonical dual-number additive group structure. -/
instance instAddCommGroup_tangentSpace [hRS : HasStrongRimSchlessinger X] :
    AddCommGroup (CategoryTheory.Functor.tangentSpace (predeformationFunctor X openImmersion kToS h_factor x0)) :=
  CategoryTheory.Functor.instAddCommGroup_fiberDualTangent
    (predeformationFunctor X openImmersion kToS h_factor x0)

/-- The tangent quotient has its canonical dual-number scalar action. -/
instance instModule_tangentSpace [hRS : HasStrongRimSchlessinger X] :
    Module k (CategoryTheory.Functor.tangentSpace (predeformationFunctor X openImmersion kToS h_factor x0)) :=
  CategoryTheory.Functor.instModule_fiberDualTangent
    (predeformationFunctor X openImmersion kToS h_factor x0)

/-- The tangent space of residue lifts is linearly equivalent to the geometric tangent space. -/
def tangentSpaceEquiv [hRS : HasStrongRimSchlessinger X] :
    (CategoryTheory.Functor.tangentSpace (predeformationFunctor X openImmersion kToS h_factor x0)) ≃ₗ[k]
      ((tangentFunctor x0).obj (ModuleCat.of k k) : Type (u + 1)) := by
  let e := tangentSpaceTypeEquiv openImmersion kToS h_factor X x0
  have laws : (∀ a b, e (a + b) = e a + e b) ∧
      (∀ (r : k) a, e (r • a) = r • e a) := sorry
  exact { e with map_add' := laws.1, map_smul' := laws.2 }

/-- `tangentSpaceEquiv` sends the class of a dual-number fibre object to the class of the
corresponding lift. -/
theorem tangentSpaceEquiv_mk [hRS : HasStrongRimSchlessinger X]
    (ξ : ((predeformationFunctor X openImmersion kToS h_factor x0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k))) :
    tangentSpaceEquiv openImmersion kToS h_factor X x0
        (CategoryTheory.Functor.tangentSpace.mk (predeformationFunctor X openImmersion kToS h_factor x0) ξ) =
      (tangentForget x0 (ModuleCat.of k k)).symm
        (lifts.mk (dualNumberFiberToLift openImmersion kToS h_factor X x0 ξ)) :=
  sorry

/-- The reverse of `tangentSpaceEquiv` sends the class of a lift to the class of the
corresponding dual-number fibre object. -/
theorem tangentSpaceEquiv_symm_mk [hRS : HasStrongRimSchlessinger X]
    (a : liftCat x0 (trivSqZeroHom (CommRingCat.of k) (ModuleCat.of k k))
      (trivSqZeroHom_comp kToS (ModuleCat.of k k))) :
    (tangentSpaceEquiv openImmersion kToS h_factor X x0).symm
        ((tangentForget x0 (ModuleCat.of k k)).symm (lifts.mk a)) =
      CategoryTheory.Functor.tangentSpace.mk (predeformationFunctor X openImmersion kToS h_factor x0)
        (liftToDualNumberFiber openImmersion kToS h_factor X x0 a) :=
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

/-- Transport a fibre automorphism of the dual-number pullback to an automorphism of the
trivial deformation of `x0` to `k[ε]`. -/
def pullbackAutToTrivialAut
    (α : Aut (dualNumberPullback openImmersion kToS h_factor X x0)) :
    Aut (trivialDeformation x0 (ModuleCat.of k k)) :=
  let e := dualNumberPullbackIso openImmersion kToS h_factor X x0
  let c := (Chosen.Reindex.specifiedCompIsoApp X.p
      (specDualNumberIso openImmersion kToS h_factor).hom
      (specDualNumberIso openImmersion kToS h_factor).inv
      (𝟙 (Over.mk (specTrivSqZero kToS (ModuleCat.of k k))))
      (specDualNumberIso openImmersion kToS h_factor).inv_hom_id
      (trivialDeformation x0 (ModuleCat.of k k))).symm.trans
    (Chosen.Reindex.eqId.isoApp X.p
      (𝟙 (Over.mk (specTrivSqZero kToS (ModuleCat.of k k)))) rfl
      (trivialDeformation x0 (ModuleCat.of k k)))
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
def infinitesimalAutTypeEquiv [hRS : HasStrongRimSchlessinger X] :
    (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) ≃
      ((infFunctor x0).obj (ModuleCat.of k k) : Type u) := by
  let forward := pullbackAutToTrivialAut openImmersion kToS h_factor X x0
  let backward := trivialAutToPullbackAut openImmersion kToS h_factor X x0
  have laws :
      (∀ α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
          (dualNumberPullback openImmersion kToS h_factor X x0)
          (dualNumberPullbackHom openImmersion kToS h_factor X x0),
        (trivialDeformationLift x0 (ModuleCat.of k k)).hom ≫
            Fiber.fiberInclusion.map (forward α.1).hom =
          (trivialDeformationLift x0 (ModuleCat.of k k)).hom) ∧
      (∀ β : (infFunctor x0).obj (ModuleCat.of k k),
        backward β.1 ∈ infinitesimalAutomorphisms openImmersion kToS h_factor X x0
          (dualNumberPullback openImmersion kToS h_factor X x0)
          (dualNumberPullbackHom openImmersion kToS h_factor X x0)) ∧
      (∀ α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
          (dualNumberPullback openImmersion kToS h_factor X x0)
          (dualNumberPullbackHom openImmersion kToS h_factor X x0),
        backward (forward α.1) = α.1) ∧
      (∀ β : (infFunctor x0).obj (ModuleCat.of k k), forward (backward β.1) = β.1) := sorry
  exact
    { toFun := fun α ↦ ⟨forward α.1, laws.1 α⟩
      invFun := fun β ↦ ⟨backward β.1, laws.2.1 β⟩
      left_inv := fun α ↦ Subtype.ext (laws.2.2.1 α)
      right_inv := fun β ↦ Subtype.ext (laws.2.2.2 β) }

/-- The additive group structure on `Inf(ℱ_{X,k,x0})` transported from `Inf_{x0}(k)`. -/
instance instAddCommGroup_infinitesimalAut [hRS : HasStrongRimSchlessinger X] :
    AddCommGroup
      (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) :=
  Equiv.addCommGroup
    (infinitesimalAutTypeEquiv openImmersion kToS h_factor X x0)

/-- The `k`-module structure on `Inf(ℱ_{X,k,x0})` transported from `Inf_{x0}(k)`. -/
instance instModule_infinitesimalAut [hRS : HasStrongRimSchlessinger X] :
    Module k
      (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) :=
  Equiv.module k
    (infinitesimalAutTypeEquiv openImmersion kToS h_factor X x0)

/-- Identification of `Inf(ℱ_{X,k,x0})` with `Inf_{x0}(k)` as `k`-vector spaces. -/
def infinitesimalAutEquiv [hRS : HasStrongRimSchlessinger X] :
    (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) ≃ₗ[k]
      ((infFunctor x0).obj (ModuleCat.of k k) : Type u) :=
  Equiv.linearEquiv k
    (infinitesimalAutTypeEquiv openImmersion kToS h_factor X x0)

/-- `infinitesimalAutEquiv` acts by transporting the underlying automorphism along the
pullback comparison with the trivial deformation. -/
theorem infinitesimalAutEquiv_apply [hRS : HasStrongRimSchlessinger X]
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    (infinitesimalAutEquiv openImmersion kToS h_factor X x0 α).1 =
      pullbackAutToTrivialAut openImmersion kToS h_factor X x0 α.1 :=
  sorry

/-- `infinitesimalAutEquiv` identifies the subgroup multiplication of
`Inf(ℱ_{X,k,x0})` with addition in `Inf_{x0}(k)`. -/
theorem infinitesimalAutEquiv_mul [hRS : HasStrongRimSchlessinger X]
    (α β : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    infinitesimalAutEquiv openImmersion kToS h_factor X x0 (α * β) =
      infinitesimalAutEquiv openImmersion kToS h_factor X x0 α +
        infinitesimalAutEquiv openImmersion kToS h_factor X x0 β :=
  sorry

/-- The image of a fibre automorphism under `infinitesimalAutEquiv` satisfies the
equalizer condition defining `infType`. -/
theorem infinitesimalAutEquiv_mem [hRS : HasStrongRimSchlessinger X]
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    (infinitesimalAutEquiv openImmersion kToS h_factor X x0 α).1.hom.1 ≫
        Chosen.cartesianHom X.p (specOverInl kToS (ModuleCat.of k k)) x0 =
      Chosen.cartesianHom X.p (specOverInl kToS (ModuleCat.of k k)) x0 :=
  sorry

/-- Scaling the nilpotent coordinate fixes the projection to the residue spectrum. -/
theorem dualNumberScale_comp_toResidue (r : k) :
    specOverMap openImmersion (ArtinianLocalAlgCat.dualNumberScaleHom Λ r) ≫
        specDualNumberToResidue openImmersion k kToS h_factor =
      specDualNumberToResidue openImmersion k kToS h_factor := sorry

/-- Pulling the trivial dual-number pullback along scaling gives the same pullback. -/
def dualNumberPullbackScaleIso (r : k) :
    Chosen.reindexObj X.p
        (specOverMap openImmersion (ArtinianLocalAlgCat.dualNumberScaleHom Λ r))
        (dualNumberPullback openImmersion kToS h_factor X x0) ≅
      dualNumberPullback openImmersion kToS h_factor X x0 :=
  (Chosen.Reindex.specifiedCompIsoApp X.p
    (specDualNumberToResidue openImmersion k kToS h_factor)
    (specOverMap openImmersion (ArtinianLocalAlgCat.dualNumberScaleHom Λ r))
    (specDualNumberToResidue openImmersion k kToS h_factor)
    (dualNumberScale_comp_toResidue openImmersion kToS h_factor r) x0).symm

/-- Geometric scaling of a dual-number automorphism is reindexing followed by conjugation
with the canonical pullback comparison. -/
def dualNumberPullbackScaleAut (r : k)
    (α : Aut (dualNumberPullback openImmersion kToS h_factor X x0)) :
    Aut (dualNumberPullback openImmersion kToS h_factor X x0) :=
  let e := dualNumberPullbackScaleIso openImmersion kToS h_factor X x0 r
  e.symm ≪≫
    (Chosen.reindex X.p
      (specOverMap openImmersion (ArtinianLocalAlgCat.dualNumberScaleHom Λ r))).mapIso α ≪≫ e

/-- Geometric scaling preserves the subgroup of automorphisms fixing the residue section. -/
theorem dualNumberPullbackScaleAut_mem (r : k)
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    dualNumberPullbackScaleAut openImmersion kToS h_factor X x0 r α.1 ∈
      infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) := sorry

/-- The geometric scalar operation on infinitesimal automorphisms is induced by scaling
the nilpotent coordinate of the dual numbers. -/
def infinitesimalAutScale (r : k)
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0) :=
  ⟨dualNumberPullbackScaleAut openImmersion kToS h_factor X x0 r α.1,
    dualNumberPullbackScaleAut_mem openImmersion kToS h_factor X x0 r α⟩

/-- Scalar multiplication on infinitesimal automorphisms agrees with geometric
scaling of the nilpotent coordinate. -/
theorem infinitesimalAut_smul_eq_scale [hRS : HasStrongRimSchlessinger X] (r : k)
    (α : infinitesimalAutomorphisms openImmersion kToS h_factor X x0
      (dualNumberPullback openImmersion kToS h_factor X x0)
      (dualNumberPullbackHom openImmersion kToS h_factor X x0)) :
    r • α = infinitesimalAutScale openImmersion kToS h_factor X x0 r α := sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
