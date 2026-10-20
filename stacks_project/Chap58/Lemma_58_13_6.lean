/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueGalois
import ReasLib.FieldTheory.Galois.IntegralClosure.SeparableTame

@[expose] public section

open scoped Pointwise
open Ideal IsLocalRing

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
variable (Ksep : Type w) [Field Ksep] [Algebra A Ksep] [Algebra K Ksep]
  [IsScalarTower A K Ksep] [IsSepClosure K Ksep]

/- Lemma 58.13.6 (1): the branch residue field is an algebraic closure of the base residue field. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.isAlgClosure_residueField K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    -- Local instance justification (defeq pin): the check uses the canonical base-to-branch residue algebra of the closure theorem.
    letI := integralClosure.ResidueField.algebraOfBase m
    -- Local instance justification (search instability): select the canonical vector-space torsion-free instance directly because synthesis after the tame imports exhausts its heartbeat limit.
    letI : Module.IsTorsionFree (maximalIdeal A).ResidueField m.ResidueField :=
      DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure (maximalIdeal A).ResidueField m.ResidueField)

/- Lemma 58.13.6 (2): the decomposition-group residue action has inertia as kernel. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.residueGaloisHom_ker K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    (integralClosure.SepClosure.residueGaloisHom K Ksep m).ker =
      m.inertia (MulAction.stabilizer Gal(Ksep/K) m))

/- Lemma 58.13.6 (3): the decomposition group surjects onto the residue Galois group. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.residueGaloisHom_surjective K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    Function.Surjective (integralClosure.SepClosure.residueGaloisHom K Ksep m))

variable (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]

/- Lemma 58.13.6 (4): the wild-to-inertia-to-tame sequence is exact. -/
@[stacks 0BUB] #check (integralClosure.profiniteTameExtension K m :
  GroupExtension (integralClosure.profiniteWildInertia K m) (m.inertia Gal(Ksep/K))
    (integralClosure.profiniteTameInertia K m))
@[stacks 0BUB] #check (GroupExtension.range_inl_eq_ker_rightHom (integralClosure.profiniteTameExtension K m) :
  (integralClosure.profiniteTameExtension K m).inl.range =
    (integralClosure.profiniteTameExtension K m).rightHom.ker)

/- Lemma 58.13.6 (5): wild inertia is normal in the decomposition group. -/
@[stacks 0BUB] #check (integralClosure.profiniteWildInertia_normal_in_stabilizer K :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    (((integralClosure.profiniteWildInertia K m).map (m.inertia Gal(Ksep/K)).subtype).subgroupOf
      (MulAction.stabilizer Gal(Ksep/K) m)).Normal)

/- Lemma 58.13.6 (6): wild inertia is trivial in residue characteristic zero. -/
@[stacks 0BUB] #check (integralClosure.wildInertia_eq_bot_of_char_zero K :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    ringChar (maximalIdeal A).ResidueField = 0 →
      integralClosure.profiniteWildInertia K m = ⊥)

/- Lemma 58.13.6 (7): wild inertia is a pro-p group in positive residue characteristic. -/
@[stacks 0BUB] #check (integralClosure.wildInertia_isProPGroup K :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal) {p : ℕ},
    ringChar (maximalIdeal A).ResidueField = p → 1 < p →
      ∀ (U : OpenNormalSubgroup (integralClosure.profiniteWildInertia K m)),
        IsPGroup p ((integralClosure.profiniteWildInertia K m) ⧸ U.toSubgroup))

/- Lemma 58.13.6 (8): the canonical full tame character is surjective. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.thetaCan_surjective K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    Function.Surjective (integralClosure.SepClosure.thetaCan K Ksep m))

/- Lemma 58.13.6 (9): the full tame character has wild inertia as kernel. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.thetaCan_ker K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    (integralClosure.SepClosure.thetaCan K Ksep m).ker = integralClosure.profiniteWildInertia K m)

/- Lemma 58.13.6 (10): the tame character is equivariant under decomposition-group conjugation. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.thetaCan_conj K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal)
    (τ : MulAction.stabilizer Gal(Ksep/K) m) (σ : m.inertia Gal(Ksep/K))
    (order : integralClosure.SepClosure.primeToIndex A),
    -- Local instance justification (defeq pin): the check uses the canonical residue algebra of the residue Galois roots-of-unity action.
    letI := integralClosure.ResidueField.algebraOfBase m
    (integralClosure.SepClosure.tameRoots Ksep m).subtype
        (integralClosure.SepClosure.thetaCan K Ksep m (Ideal.inertiaConjHom m τ σ)) order =
      (integralClosure.SepClosure.residueGaloisHom K Ksep m τ).toMulEquiv.restrictRootsOfUnity order.1
        ((integralClosure.SepClosure.tameRoots Ksep m).subtype
          (integralClosure.SepClosure.thetaCan K Ksep m σ) order))

/- Lemma 58.13.6 (11): the tame quotient is isomorphic to the full roots-of-unity limit. -/
@[stacks 0BUB] #check (integralClosure.SepClosure.tameQuotientHom_bijective K Ksep :
  ∀ (m : Ideal (integralClosure A Ksep)) (_ : m.IsMaximal),
    Function.Bijective (integralClosure.SepClosure.tameQuotientHom K Ksep m))
