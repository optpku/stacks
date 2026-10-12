/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap90.Lemma_90_10_7_Pullback
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap98.«98_3_0_2»
public import stacks_project.Chap98.«98_8_0_1_TangentSpace»
public import stacks_project.Chap98.«98_9_3_1»
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Example_98_13_2_Groupoids
public import stacks_project.Chap98.Example_98_13_2_Predicate
public import stacks_project.Chap98.Lemma_98_3_1
public import stacks_project.Chap98.Lemma_98_3_3_Predeformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Example 98.13.2: a category fibred in groupoids satisfying Artin axioms [0]–[4] but not [5]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.ArtinVersalityCounterexample
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open Functor.Fiber TrivSqZeroExt
open scoped AlgebraicGeometry Bicategory DualNumber

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Example 98.13.2 (1): geometrically `HasF φ` means there is a quasi-compact open
neighbourhood of `V(s, t) ⊆ Spec(A)` on which `s` vanishes. -/
@[stacks 07XR]
theorem hasF_iff_exists_qcOpen {A : Type u} [CommRing A] (φ : coordRing k →+* A) :
    HasF φ ↔ ExistsQcOpen φ :=
  sorry

/-- Example 98.13.2 (2): `X` is the full subcategory of schemes over `Spec(Λ)` that
admit an affine open cover on which `HasF` holds. -/
@[stacks 07XR]
theorem groupoids_eq_covered :
    (groupoids k).p = ObjectProperty.ι (IsCovered k) :=
  sorry

/-- Example 98.13.2 (3): `X` is a stack in groupoids for the étale topology. -/
@[stacks 07XR, instance]
instance instIsStackInGroupoids_etale :
    IsStack.InGroupoids (Scheme.etaleTopology.over (baseScheme k)) (groupoids k).p :=
  sorry

/-- Example 98.13.2 (4): `X` is limit preserving: for a directed inverse system of
affine schemes over `Spec(Λ)` with affine limit `T`, the functor
`colim X_{T_i} ⟶ X_T` of fibre categories is an equivalence. -/
@[stacks 07XR, instance]
instance instLimitPreserving :
    AlgebraicGeometry.Groupoids.LimitPreserving (groupoids k) :=
  sorry

/-- Example 98.13.2 (5): `X` satisfies the Rim–Schlessinger condition (RS). -/
@[stacks 07XR, instance]
instance instHasRimSchlessinger :
    HasRimSchlessinger (groupoids k) :=
  sorry

/-- The identity chart `Spec(Λ) ⟶ Spec(Λ)`. -/
abbrev identityChart : Spec (CommRingCat.of (coordRing k)) ⟶ baseScheme k :=
  𝟙 (baseScheme k)

/-- The identity chart is the identity morphism of `Spec(Λ)`. -/
theorem identityChart_eq : identityChart k = 𝟙 (baseScheme k) :=
  sorry

/-- The identity chart is an open immersion. -/
instance instIsOpenImmersion_identityChart : IsOpenImmersion (identityChart k) :=
  inferInstance

/-- The morphism `Spec(k') ⟶ Spec(Λ)` associated to a finite type `Λ`-field `k'`. -/
def fieldToBase (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    Spec (CommRingCat.of k') ⟶ baseScheme k :=
  (specOver (identityChart k) (ArtinianLocalAlgCat.residue (coordRing k) k')).hom

/-- `fieldToBase` is the structure morphism of `specOver` of the residue field. -/
theorem fieldToBase_eq (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    fieldToBase k k' =
      (specOver (identityChart k) (ArtinianLocalAlgCat.residue (coordRing k) k')).hom :=
  sorry

/-- The identity chart `Spec(Λ) ⟶ Spec(Λ)` factors the residue morphism of `k'`. -/
theorem fieldToBase_factor (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    Spec.map (CommRingCat.ofHom (algebraMap (coordRing k) k')) ≫ identityChart k =
      fieldToBase k k' :=
  sorry

/-- A finite type `Λ`-algebra structure on a field yields a locally finite type
morphism `Spec(k') ⟶ Spec(Λ)`. -/
instance instLocallyOfFiniteType_fieldToBase (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k'] :
    LocallyOfFiniteType (fieldToBase k k') :=
  sorry

/-- The predeformation functor `ℱ_{X, k', x0}` relative to the identity chart of
`Spec(Λ)`. -/
abbrev predeformationAt (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :=
  predeformationFunctor (groupoids k) (identityChart k) (fieldToBase k k')
    (fieldToBase_factor k k') x0

/-- `predeformationAt` is the CFG-associated predeformation functor on the identity
chart. -/
theorem predeformationAt_eq (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    predeformationAt k k' x0 =
      predeformationFunctor (groupoids k) (identityChart k) (fieldToBase k k')
        (fieldToBase_factor k k') x0 :=
  sorry

/-- The tangent space of `ℱ_{X, k', x0}` on the identity chart. -/
abbrev tangentSpaceAt (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :=
  tangentSpace (identityChart k) (fieldToBase k k') (fieldToBase_factor k k')
    (groupoids k) x0

/-- Dual-number scaling `a + v ε ↦ a + (c v) ε` as a `Λ`-algebra map. -/
def dualNumberScaleAlgHom (k' : Type u) [Field k'] [Algebra (coordRing k) k'] (c : k') :
    DualNumber k' →ₐ[coordRing k] DualNumber k' where
  toFun x := inl x.fst + inr (c * x.snd)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Dual-number scaling evaluates to `inl x.fst + inr (c * x.snd)`. -/
theorem dualNumberScaleAlgHom_apply (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    (c : k') (x : DualNumber k') :
    dualNumberScaleAlgHom k k' c x = inl x.fst + inr (c * x.snd) :=
  sorry

/-- Dual-number scaling as a morphism of `ArtinianLocalAlgCat`. -/
def dualNumberScaleHom (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] (c : k') :
    ArtinianLocalAlgCat.dualNumber (coordRing k) k' ⟶
      ArtinianLocalAlgCat.dualNumber (coordRing k) k' where
  hom := dualNumberScaleAlgHom k k' c
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberScaleHom` is `dualNumberScaleAlgHom`. -/
theorem dualNumberScaleHom_hom (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] (c : k') :
    (dualNumberScaleHom k k' c).hom = dualNumberScaleAlgHom k k' c :=
  sorry

/-- Dual-number addition `k[ε] ×_k k[ε] ⟶ k[ε]`, sending a pair of dual numbers with
the same residue to the dual number whose infinitesimal coefficient is the sum. -/
def dualNumberAddAlgHom (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    (ArtinianLocalAlgCat.dualNumberPullback
        (ArtinianLocalAlgCat.dualNumber (coordRing k) k')).carrier →ₐ[coordRing k]
      DualNumber k' where
  toFun p :=
    let a :=
      (ArtinianLocalAlgCat.dualNumberPullbackFst
        (ArtinianLocalAlgCat.dualNumber (coordRing k) k')).hom p
    let b :=
      (ArtinianLocalAlgCat.dualNumberPullbackSnd
        (ArtinianLocalAlgCat.dualNumber (coordRing k) k')).hom p
    inl a.fst + inr (a.snd + b.snd)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Dual-number addition as a morphism of `ArtinianLocalAlgCat`. -/
def dualNumberAddHom (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    ArtinianLocalAlgCat.dualNumberPullback
        (ArtinianLocalAlgCat.dualNumber (coordRing k) k') ⟶
      ArtinianLocalAlgCat.dualNumber (coordRing k) k' where
  hom := dualNumberAddAlgHom k k'
  isLocalHom := sorry
  residue_compat := sorry

/-- The residue object of `ℱ_{X, k', x0}` is the identity morphism of `x0` over
`Spec(k')`. -/
def residuePreObj (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    Obj (identityChart k) (fieldToBase k k') (fieldToBase_factor k k') (groupoids k) x0 where
  base := ArtinianLocalAlgCat.residue (coordRing k) k'
  target := x0
  fromResidue := 𝟙 _
  over_fromResidue := sorry

/-- The residue fibre object of `ℱ_{X, k', x0}`. -/
def residueFiber (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k') :=
  ⟨residuePreObj k k' x0, rfl⟩

/-- The zero tangent vector is the dual-number pushforward of the residue object. -/
def tangentSpaceZero (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    tangentSpaceAt k k' x0 :=
  tangentSpace.mk (identityChart k) (fieldToBase k k') (fieldToBase_factor k k')
    (groupoids k) x0
    (pushforwardFiberObj (predeformationAt k k' x0)
      (cleavageOp (predeformationAt k k' x0))
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') (residueFiber k k' x0))

/-- Scalar multiplication on `Tℱ_{X, k', x0}` by dual-number pushforward along
`ε ↦ c ε`. -/
def smulTangent (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) (c : k')
    (x : tangentSpaceAt k k' x0) : tangentSpaceAt k k' x0 :=
  (pushforwardFiberFunctor (predeformationAt k k' x0)
      (cleavageOp (predeformationAt k k' x0))
      (dualNumberScaleHom k k' c)).isoClassesMap x

/-- Addition on `Tℱ_{X, k', x0}`: push the first summand along the split dual-number
section into `k[ε] ×_k k[ε]`, push the second summand along the same section after
scaling by `1`, then apply dual-number addition. -/
def addTangent (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (x _ : tangentSpaceAt k k' x0) : tangentSpaceAt k k' x0 :=
  (pushforwardFiberFunctor (predeformationAt k k' x0)
      (cleavageOp (predeformationAt k k' x0))
      (dualNumberAddHom k k')).isoClassesMap
    ((pushforwardFiberFunctor (predeformationAt k k' x0)
        (cleavageOp (predeformationAt k k' x0))
        (ArtinianLocalAlgCat.dualNumberPullbackSection
          (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))).isoClassesMap
      (smulTangent k k' x0 (1 : k') x))

/-- `addTangent` pushes a unit scaling of the first summand along the split
dual-number section and then along dual-number addition. -/
theorem addTangent_eq (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (x y : tangentSpaceAt k k' x0) :
    addTangent k k' x0 x y =
      (pushforwardFiberFunctor (predeformationAt k k' x0)
          (cleavageOp (predeformationAt k k' x0))
          (dualNumberAddHom k k')).isoClassesMap
        ((pushforwardFiberFunctor (predeformationAt k k' x0)
            (cleavageOp (predeformationAt k k' x0))
            (ArtinianLocalAlgCat.dualNumberPullbackSection
              (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))).isoClassesMap
          (smulTangent k k' x0 (1 : k') x)) :=
  sorry

/-- Zero tangent vector. -/
instance instZero_tangentSpace (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    Zero (tangentSpaceAt k k' x0) where
  zero := tangentSpaceZero k k' x0

/-- Addition of tangent vectors. -/
instance instAdd_tangentSpace (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    Add (tangentSpaceAt k k' x0) where
  add := addTangent k k' x0

/-- Negation of tangent vectors by scaling with `-1`. -/
instance instNeg_tangentSpace (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    Neg (tangentSpaceAt k k' x0) where
  neg x := smulTangent k k' x0 (-1 : k') x

/-- Additive structure on `Tℱ_{X, k', x0}`. -/
instance instAddCommGroup_tangentSpace (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    AddCommGroup (tangentSpaceAt k k' x0) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  nsmul_zero := sorry
  nsmul_succ := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

/-- `Tℱ_{X, k', x0}` is a `k'`-vector space, with scalars acting by dual-number
pushforward. -/
instance instModule_tangentSpace (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    Module k' (tangentSpaceAt k k' x0) where
  smul := smulTangent k k' x0
  one_smul := sorry
  zero_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  mul_smul := sorry

/-- Example 98.13.2 (6): for every finite type field `k'` over `Spec(Λ)` and object
`x0` of `X` over `Spec(k')`, the tangent space of `ℱ_{X, k', x0}` is finite
dimensional as a `k'`-vector space. -/
@[stacks 07XR]
theorem finiteDimensional_tangent (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    FiniteDimensional k' (tangentSpaceAt k k' x0) :=
  sorry

/-- Zero infinitesimal automorphism. -/
instance instZero_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    Zero (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) where
  zero := 1

/-- Addition of infinitesimal automorphisms by composition. -/
instance instAdd_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    Add (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) where
  add a b := a * b

/-- Negation of infinitesimal automorphisms by inversion. -/
instance instNeg_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    Neg (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) where
  neg a := a⁻¹

/-- The group of infinitesimal automorphisms is an additive group, with addition equal
to composition. -/
instance instAddCommGroup_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    AddCommGroup (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  nsmul_zero := sorry
  nsmul_succ := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

/-- Scalar multiplication on infinitesimal automorphisms by dual-number scaling of
the underlying automorphism. -/
def smulInfAut (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ]
    (c : k') (a : infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) :
    infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ :=
  let _scale := dualNumberScaleHom k k' c
  ⟨a.1, sorry⟩

/-- Infinitesimal automorphisms form a `k'`-vector space. -/
instance instModule_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    Module k' (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) where
  smul := smulInfAut k k' x0 ξ0 ξ0' φ
  one_smul := sorry
  zero_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  mul_smul := sorry

/-- Example 98.13.2 (7): for every finite type field `k'` over `Spec(Λ)` and object
`x0` of `X` over `Spec(k')`, the group of infinitesimal automorphisms of
`ℱ_{X, k', x0}` is finite dimensional as a `k'`-vector space. -/
@[stacks 07XR]
theorem finiteDimensional_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    FiniteDimensional k'
      (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) :=
  sorry

/-- Example 98.13.2 (8): every formal object of `X` is effective, and an object over
a complete local `S`-algebra is determined up to isomorphism by its restriction
system. -/
@[stacks 07XR, instance]
instance instApproximationIsEquivalence :
    (approximation (groupoids k)).IsEquivalence :=
  sorry

/-- `U` belongs to `X`. -/
theorem testOver_isCovered : IsCovered k (testOver k) :=
  sorry

/-- The identity object of `X` over `U`. -/
def identityObject : (groupoids k).total :=
  ⟨testOver k, testOver_isCovered k⟩

/-- The identity object of `X` over `U` lies over `U ⟶ Spec(Λ)`. -/
theorem identityObject_over :
    (groupoids k).p.obj (identityObject k) = Over.mk (testToBase k) :=
  sorry

/-- Example 98.13.2 (9): over `U = Spec(k[s, t] / (s))` the identity object of `X` is
versal at the origin `u0 = (s, t)` and at no other finite type point. -/
@[stacks 07XR]
theorem exists_versal_only_at_origin :
    IsFiniteTypePoint (origin k) ∧
      IsVersalAt (testToBase k) (identityObject k) (identityObject_over k) (origin k) ∧
        ∀ u : testScheme k, IsFiniteTypePoint u → u ≠ origin k →
          ¬ IsVersalAt (testToBase k) (identityObject k) (identityObject_over k) u :=
  sorry
