module

import StacksCheckRecall
import ReasLib.FieldTheory.Galois.IntegralClosure.ProfiniteTame

@[expose] public section

open scoped Pointwise
open Ideal IsLocalRing Ideal.ResidueField.Invariant

universe u v w

namespace integralClosure

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [IsGalois K L]

/- Lemma 58.13.5 -/
@[stacks 0BUA] #check
  (integralClosure.thetaCan K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    m.inertia Gal(L/K) →*
      integralClosure.TameRoots.limit m.ResidueField
        (integralClosure.tameRootIndex K m))

#check (integralClosure.tameRootIndex K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal), Set ℕ)
#check (integralClosure.mem_tameRootIndex_iff K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal) (n : ℕ),
    n ∈ integralClosure.tameRootIndex K m ↔
      ∃ level : FiniteGaloisIntermediateField K L,
        integralClosure.finiteTameOrder K m level = n)
#check (integralClosure.one_mem_tameRootIndex K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    1 ∈ integralClosure.tameRootIndex K m)
#check (integralClosure.tameRootIndex_directed K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    ∀ a ∈ integralClosure.tameRootIndex K m, ∀ b ∈ integralClosure.tameRootIndex K m,
      ∃ c ∈ integralClosure.tameRootIndex K m, a ∣ c ∧ b ∣ c)
#check (integralClosure.tameRootIndex_coprime K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal) {n p : ℕ},
    n ∈ integralClosure.tameRootIndex K m →
      ringChar (maximalIdeal A).ResidueField = p → 1 < p → Nat.Coprime n p)
#check (integralClosure.exists_primitiveRoot_of_mem_tameRootIndex K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal) {n : ℕ},
    n ∈ integralClosure.tameRootIndex K m →
      ∃ ζ : m.ResidueField, IsPrimitiveRoot ζ n)
#check (integralClosure.thetaCanPi K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    m.inertia Gal(L/K) →*
      ((n : integralClosure.tameRootIndex K m) →
        rootsOfUnity n.1 m.ResidueField))
#check (integralClosure.thetaCan_surjective K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    Function.Surjective (integralClosure.thetaCan K m))
#check (integralClosure.thetaCan_ker K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    (integralClosure.thetaCan K m).ker =
      integralClosure.profiniteWildInertia K m)
#check (integralClosure.thetaCan_conj K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal)
    (τ : MulAction.stabilizer (Gal(L/K)) m) (σ : m.inertia (Gal(L/K)))
    (n : integralClosure.tameRootIndex K m),
    (integralClosure.TameRoots.limit m.ResidueField
      (integralClosure.tameRootIndex K m)).subtype
        (integralClosure.thetaCan K m (Ideal.inertiaConjHom m τ σ)) n =
      rootsOfUnityHom (Gal(L/K)) (maximalIdeal A) m n.1 τ
        ((integralClosure.TameRoots.limit m.ResidueField
          (integralClosure.tameRootIndex K m)).subtype
          (integralClosure.thetaCan K m σ) n))
#check (integralClosure.tameQuotientHom_bijective K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    Function.Bijective (integralClosure.tameQuotientHom K m))
#check (integralClosure.ResidueField.algebraOfBase :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    Algebra (maximalIdeal A).ResidueField m.ResidueField)
#check (integralClosure.profiniteTameExtension K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    GroupExtension (integralClosure.profiniteWildInertia K m)
      (m.inertia Gal(L/K)) (integralClosure.profiniteTameInertia K m))
#check (integralClosure.TameRoots.limit :
  ∀ (κ : Type u) [CommMonoid κ] (S : Set ℕ),
    Subgroup ((n : S) → rootsOfUnity n.1 κ))

#check (integralClosure.profiniteWildInertia_normal_in_stabilizer K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    (((integralClosure.profiniteWildInertia K m).map (m.inertia Gal(L/K)).subtype).subgroupOf
      (MulAction.stabilizer Gal(L/K) m)).Normal)
#check (integralClosure.profiniteWildInertia_isClosed K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    IsClosed (integralClosure.profiniteWildInertia K m : Set (m.inertia Gal(L/K))))
#check (integralClosure.wildInertia_eq_bot_of_char_zero K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal),
    ringChar (maximalIdeal A).ResidueField = 0 →
      integralClosure.profiniteWildInertia K m = ⊥)
#check (integralClosure.wildInertia_isProPGroup K :
  ∀ (m : Ideal (integralClosure A L)) (_ : m.IsMaximal) {p : ℕ},
    ringChar (maximalIdeal A).ResidueField = p → 1 < p →
      ∀ U : OpenNormalSubgroup (integralClosure.profiniteWildInertia K m),
        IsPGroup p ((integralClosure.profiniteWildInertia K m) ⧸ U.toSubgroup))

section ResidueAction

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

#check (integralClosure.ResidueField.stabilizerHom_surjective (K := K) (maximalIdeal A) m :
  Function.Surjective (Ideal.ResidueField.Invariant.stabilizerHom
    (Gal(L/K)) (maximalIdeal A) m))
#check (
  -- Local instance justification (defeq pin): use the residue algebra selected by the canonical stabilizerHom whose kernel is checked.
  letI : Algebra (maximalIdeal A).ResidueField m.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) m
  -- Local instance justification (defeq pin): use the quotient-to-residue algebra occurring in the definition of that same stabilizerHom.
  letI : Algebra (A ⧸ maximalIdeal A) m.ResidueField :=
    Ideal.ResidueField.LiesOver.quotientAlgebra (maximalIdeal A) m
  -- Local instance justification (defeq pin): match the residue scalar tower used to lift the quotient action in stabilizerHom.
  letI : IsScalarTower (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField m.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_residue (maximalIdeal A) m
  -- Local instance justification (defeq pin): match the quotient scalar tower used by the same fraction-field action lift.
  letI : IsScalarTower (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) m.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_quotient (maximalIdeal A) m
  (IsFractionRing.ker_stabilizerHom (Gal(L/K)) (maximalIdeal A) m
    (maximalIdeal A).ResidueField m.ResidueField :
    (Ideal.ResidueField.Invariant.stabilizerHom (Gal(L/K)) (maximalIdeal A) m).ker =
      m.inertia (MulAction.stabilizer Gal(L/K) m)))

end ResidueAction

end integralClosure
