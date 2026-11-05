/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueField
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower.ResidueField
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.Invariant.ResidueField.RootsOfUnity
public import ReasLib.RingTheory.RootsOfUnity.Limit
public import ReasLib.Topology.Algebra.OpenNormalSubgroup

@[expose] public section

open scoped Pointwise
open Ideal IsLocalRing Ideal.ResidueField.Invariant

universe u v w

namespace integralClosure

namespace TameRoots

/-- Compatibility alias for the former consumer-specific name of the roots-of-unity limit. -/
@[deprecated rootsOfUnity.limit (since := "2026-11-04")]
abbrev limit (κ : Type u) [CommMonoid κ] (S : Set ℕ) :
    Subgroup ((n : S) → rootsOfUnity n.1 κ) := rootsOfUnity.limit κ S

end TameRoots

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [IsGalois K L]

/-- The contraction of a maximal branch to a finite Galois intermediate field. -/
noncomputable abbrev finiteTameBranch
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (level : FiniteGaloisIntermediateField K L) : Ideal (integralClosure A level) :=
  let htower : IsScalarTower A level.toIntermediateField L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  @Tower.under A level.toIntermediateField L _ _ _ _ _ _ htower m

/-- The order of the tame inertia quotient at a finite Galois branch. -/
noncomputable abbrev finiteTameOrder
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (level : FiniteGaloisIntermediateField K L) : ℕ :=
  Nat.card ((finiteTameBranch K m level).tameInertia Gal(level/K))

/-- The tame inertia quotient at a finite Galois branch has nonzero order. -/
theorem finiteTameOrder_ne_zero (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (level : FiniteGaloisIntermediateField K L) : finiteTameOrder K m level ≠ 0 := sorry

/-- Inclusion of finite Galois levels implies divisibility of their tame orders. -/
theorem finiteTameOrder_dvd_of_le (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (lower upper : FiniteGaloisIntermediateField K L) (hle : lower ≤ upper) :
    finiteTameOrder K m lower ∣ finiteTameOrder K m upper := sorry

/-- Restriction of inertia to a finite Galois intermediate field. -/
noncomputable def finiteInertiaHom (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (level : FiniteGaloisIntermediateField K L) :
    m.inertia Gal(L/K) →* (finiteTameBranch K m level).inertia Gal(level/K) :=
  let htower : IsScalarTower A level.toIntermediateField L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  @Tower.inertiaHom A K level.toIntermediateField L _ _ _ _ _ _ _ _ _ _ _ _ _ _ htower m

/-- The finite tame character embedded in the residue field of the full branch. -/
noncomputable def finiteTameCharacter
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (level : FiniteGaloisIntermediateField K L) :
    m.inertia Gal(L/K) →* rootsOfUnity (finiteTameOrder K m level) m.ResidueField :=
  let htower : IsScalarTower A level.toIntermediateField L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let hmax : (finiteTameBranch K m level).IsMaximal :=
    @Tower.under_isMaximal A level.toIntermediateField L _ _ _ _ _ _ htower m inferInstance
  (restrictRootsOfUnity
    (@Tower.residueMap A level.toIntermediateField L _ _ _ _ _ _ htower m inferInstance)
    (finiteTameOrder K m level)).comp
      ((@Tame.scaledCharacter A _ _ _ K _ _ _ level.toIntermediateField _ _ _ _ _ _
          (finiteTameBranch K m level) hmax).comp
        (finiteInertiaHom K m level))

/-- Finite tame characters are compatible under the power map between dividing tame orders. -/
theorem finiteTameCharacter_compatible
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (lower upper : FiniteGaloisIntermediateField K L)
    (hdiv : finiteTameOrder K m lower ∣ finiteTameOrder K m upper) :
    (rootsOfUnity.powMap hdiv).comp (finiteTameCharacter K m upper) =
      finiteTameCharacter K m lower := sorry

/-- The tame index set obtained from the orders of finite Galois levels. -/
noncomputable def tameRootIndex (m : Ideal (integralClosure A L)) [m.IsMaximal] : Set ℕ :=
  Set.range (finiteTameOrder K m)

/-- Membership in the tame index set is witnessed by a finite Galois level. -/
theorem mem_tameRootIndex_iff (m : Ideal (integralClosure A L)) [m.IsMaximal] (n : ℕ) :
    n ∈ tameRootIndex K m ↔
      ∃ level : FiniteGaloisIntermediateField K L, finiteTameOrder K m level = n := sorry

/-- The trivial finite Galois level contributes the tame order one. -/
theorem one_mem_tameRootIndex (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    1 ∈ tameRootIndex K m := sorry

/-- The tame index set is directed under divisibility. -/
theorem tameRootIndex_directed (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    ∀ a ∈ tameRootIndex K m, ∀ b ∈ tameRootIndex K m,
      ∃ c ∈ tameRootIndex K m, a ∣ c ∧ b ∣ c := sorry

/-- Finite tame orders are prime to positive residue characteristic. -/
theorem tameRootIndex_coprime (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {n p : ℕ} (hn : n ∈ tameRootIndex K m)
    (hchar : ringChar (maximalIdeal A).ResidueField = p) (hp : 1 < p) :
    Nat.Coprime n p := sorry

/-- Every finite-level tame order has a primitive root in the branch residue field. -/
theorem exists_primitiveRoot_of_mem_tameRootIndex
    (m : Ideal (integralClosure A L)) [m.IsMaximal] {n : ℕ}
    (hn : n ∈ tameRootIndex K m) :
    ∃ ζ : m.ResidueField, IsPrimitiveRoot ζ n := sorry

/-- The finite component of the canonical tame character. -/
noncomputable def thetaCanComponent
    (m : Ideal (integralClosure A L)) [m.IsMaximal] (n : tameRootIndex K m) :
    m.inertia Gal(L/K) →* rootsOfUnity n.1 m.ResidueField :=
  let level := Classical.choose n.property
  let horder := Classical.choose_spec n.property
  (congrArg (fun order ↦ m.inertia Gal(L/K) →* rootsOfUnity order m.ResidueField)
    horder).mp (finiteTameCharacter K m level)

/-- A tame character coordinate agrees with every finite level of its prescribed order. -/
theorem thetaCanComponent_spec
    (m : Ideal (integralClosure A L)) [m.IsMaximal] (n : tameRootIndex K m)
    (level : FiniteGaloisIntermediateField K L) (horder : finiteTameOrder K m level = n.1) :
    thetaCanComponent K m n =
      (congrArg (fun order ↦ m.inertia Gal(L/K) →* rootsOfUnity order m.ResidueField)
        horder).mp (finiteTameCharacter K m level) := sorry

/-- The product of the finite-level tame characters. -/
noncomputable def thetaCanPi (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.inertia Gal(L/K) →*
      ((n : tameRootIndex K m) → rootsOfUnity n.1 m.ResidueField) :=
  MonoidHom.pi (fun n ↦ thetaCanComponent K m n)

/-- The finite-level characters form a compatible roots-of-unity family. -/
theorem thetaCanPi_mem_limit (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    thetaCanPi K m σ ∈ rootsOfUnity.limit m.ResidueField (tameRootIndex K m) := sorry

/-- The canonical tame character into the compatible roots-of-unity limit. -/
noncomputable def thetaCan (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.inertia Gal(L/K) →*
      rootsOfUnity.limit m.ResidueField (tameRootIndex K m) :=
  MonoidHom.codRestrict (thetaCanPi K m)
    (rootsOfUnity.limit m.ResidueField (tameRootIndex K m))
    (thetaCanPi_mem_limit K m)

/-- Evaluation of the canonical tame character is componentwise evaluation. -/
theorem thetaCan_apply (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    (thetaCan K m σ : (n : tameRootIndex K m) → rootsOfUnity n.1 m.ResidueField) =
      thetaCanPi K m σ := sorry

/-- Profinite wild inertia consists of elements whose restrictions are wild at every finite level. -/
noncomputable def profiniteWildInertia (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Subgroup (m.inertia Gal(L/K)) :=
  ⨅ level : FiniteGaloisIntermediateField K L,
    (((finiteTameBranch K m level).wildInertia Gal(level/K)).subgroupOf
      ((finiteTameBranch K m level).inertia Gal(level/K))).comap (finiteInertiaHom K m level)

/-- Membership in profinite wild inertia is wildness of restriction at every finite Galois level. -/
theorem mem_profiniteWildInertia_iff (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    σ ∈ profiniteWildInertia K m ↔
      ∀ level : FiniteGaloisIntermediateField K L,
        (finiteInertiaHom K m level σ : Gal(level/K)) ∈
          (finiteTameBranch K m level).wildInertia Gal(level/K) := sorry

/-- Profinite wild inertia is a normal subgroup of inertia. -/
instance profiniteWildInertia_normal (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    (profiniteWildInertia K m).Normal := sorry

/-- Profinite wild inertia, mapped into the decomposition group, is normal. -/
instance profiniteWildInertia_normal_in_stabilizer
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    (((profiniteWildInertia K m).map (m.inertia Gal(L/K)).subtype).subgroupOf
      (MulAction.stabilizer Gal(L/K) m)).Normal := sorry

/-- Profinite wild inertia is closed in the inherited Krull topology on inertia. -/
theorem profiniteWildInertia_isClosed (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    IsClosed (profiniteWildInertia K m : Set (m.inertia Gal(L/K))) := sorry

/-- Profinite tame inertia is inertia modulo its finite-level wild subgroup. -/
noncomputable abbrev profiniteTameInertia (m : Ideal (integralClosure A L)) [m.IsMaximal] :=
  m.inertia Gal(L/K) ⧸ profiniteWildInertia K m

/-- The canonical exact sequence of profinite wild inertia, inertia and profinite tame inertia. -/
noncomputable def profiniteTameExtension (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    GroupExtension (profiniteWildInertia K m) (m.inertia Gal(L/K)) (profiniteTameInertia K m) :=
  { inl := (profiniteWildInertia K m).subtype
    rightHom := QuotientGroup.mk' (profiniteWildInertia K m)
    inl_injective := Subtype.coe_injective
    range_inl_eq_ker_rightHom := sorry
    rightHom_surjective := QuotientGroup.mk'_surjective _ }

/-- The canonical tame character has profinite wild inertia as its kernel. -/
theorem thetaCan_ker (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    (thetaCan K m).ker = profiniteWildInertia K m := sorry

/-- The quotient homomorphism induced by the canonical tame character. -/
noncomputable def tameQuotientHom (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    profiniteTameInertia K m →*
      rootsOfUnity.limit m.ResidueField (tameRootIndex K m) :=
  QuotientGroup.lift
    (profiniteWildInertia K m)
    (thetaCan K m)
    (thetaCan_ker K m).symm.le

/-- Evaluation of the tame quotient homomorphism on an inertia representative. -/
theorem tameQuotientHom_mk (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    tameQuotientHom K m (QuotientGroup.mk σ) = thetaCan K m σ := sorry

/-- Wild inertia is trivial in residue characteristic zero. -/
theorem wildInertia_eq_bot_of_char_zero
    (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (hchar : ringChar (maximalIdeal A).ResidueField = 0) :
    profiniteWildInertia K m = ⊥ := sorry

/-- Every open normal quotient of wild inertia is a p-group in residue characteristic p. -/
theorem wildInertia_isProPGroup (m : Ideal (integralClosure A L)) [m.IsMaximal]
    {p : ℕ} (hp : ringChar (maximalIdeal A).ResidueField = p) (hp1 : 1 < p)
    (U : OpenNormalSubgroup (profiniteWildInertia K m)) :
    IsPGroup p ((profiniteWildInertia K m) ⧸ U.toSubgroup) := sorry

/-- The canonical tame character is surjective. -/
theorem thetaCan_surjective (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Surjective (thetaCan K m) := sorry

/-- The canonical tame character is equivariant for decomposition-group conjugation. -/
theorem thetaCan_conj (m : Ideal (integralClosure A L)) [m.IsMaximal]
    (τ : MulAction.stabilizer (Gal(L/K)) m) (σ : m.inertia (Gal(L/K)))
    (n : tameRootIndex K m) :
    (rootsOfUnity.limit m.ResidueField (tameRootIndex K m)).subtype
        (thetaCan K m (Ideal.inertiaConjHom m τ σ)) n =
      rootsOfUnityHom (Gal(L/K)) (maximalIdeal A) m n.1 τ
        ((rootsOfUnity.limit m.ResidueField (tameRootIndex K m)).subtype
          (thetaCan K m σ) n) := sorry

/-- The induced tame quotient homomorphism is bijective. -/
theorem tameQuotientHom_bijective (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Function.Bijective (tameQuotientHom K m) := sorry

end integralClosure
