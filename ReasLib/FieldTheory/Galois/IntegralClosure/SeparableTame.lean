/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Logic.Function.Basic
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueGalois
public import ReasLib.FieldTheory.Galois.IntegralClosure.ProfiniteTame

@[expose] public section

open scoped Pointwise
open Ideal IsLocalRing

universe u v w

namespace integralClosure.SepClosure

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
variable (Ksep : Type w) [Field Ksep] [Algebra A Ksep] [Algebra K Ksep]
  [IsScalarTower A K Ksep] [IsSepClosure K Ksep]

/-- The positive integers prime to the residue characteristic, with all positive integers
included in residue characteristic zero. -/
def primeToIndex (A : Type u) [CommRing A] [IsLocalRing A] : Set ℕ :=
  {order | 0 < order ∧
    (ringChar (maximalIdeal A).ResidueField = 0 ∨
      order.Coprime (ringChar (maximalIdeal A).ResidueField))}

/-- The full prime-to-characteristic inverse limit of roots of unity in the residue
separable closure. -/
noncomputable abbrev tameRoots (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :=
  TameRoots.limit (residueSep Ksep m) (primeToIndex A)

/-- Every finite-level tame order is positive and prime to the base residue characteristic. -/
theorem tameRootIndex_subset (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    integralClosure.tameRootIndex K m ⊆ primeToIndex A := sorry

/-- Every positive prime-to-characteristic integer divides a finite-level tame order in a
separable closure of the fraction field. -/
theorem tameRootIndex_cofinal (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (order : ℕ) (horder : order ∈ primeToIndex A) :
    ∃ finiteOrder ∈ integralClosure.tameRootIndex K m, order ∣ finiteOrder := sorry

/-- Restriction of a full compatible family to finite tame orders, followed by inclusion
of the residue separable closure into the branch residue field. -/
noncomputable def rootsRestrictionPi (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    tameRoots Ksep m →*
      ((order : integralClosure.tameRootIndex K m) → rootsOfUnity order.1 m.ResidueField) :=
  -- Local instance justification (defeq pin): the inclusion of residueSep is the intermediate-field inclusion for the canonical base-to-branch residue algebra.
  letI := integralClosure.ResidueField.algebraOfBase m
  MonoidHom.pi (fun order ↦
    (restrictRootsOfUnity
      (separableClosure (maximalIdeal A).ResidueField m.ResidueField).val order.1).comp
      ((Pi.evalMonoidHom (fun index : primeToIndex A ↦
        rootsOfUnity index.1 (residueSep Ksep m))
        ⟨order.1, tameRootIndex_subset K Ksep m order.2⟩).comp
          (tameRoots Ksep m).subtype))

/-- Restricting a full compatible roots-of-unity family preserves compatibility at finite
tame orders. -/
theorem rootsRestrictionPi_mem (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (family : tameRoots Ksep m) :
    rootsRestrictionPi K Ksep m family ∈
      TameRoots.limit m.ResidueField (integralClosure.tameRootIndex K m) := sorry

/-- The comparison from the full prime-to-characteristic roots-of-unity limit to the
finite-level tame roots-of-unity limit. -/
noncomputable def rootsRestriction (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    tameRoots Ksep m →*
      TameRoots.limit m.ResidueField (integralClosure.tameRootIndex K m) :=
  (rootsRestrictionPi K Ksep m).codRestrict
    (TameRoots.limit m.ResidueField (integralClosure.tameRootIndex K m))
    (rootsRestrictionPi_mem K Ksep m)

/-- The full prime-to-characteristic limit and the finite-level tame limit are identified
by restriction. -/
theorem rootsRestriction_bijective (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    Function.Bijective (rootsRestriction K Ksep m) := sorry

/-- The total inverse selection for the restriction map, bundled as a group homomorphism. -/
noncomputable def rootsLift (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    TameRoots.limit m.ResidueField (integralClosure.tameRootIndex K m) →*
      tameRoots Ksep m :=
  MonoidHom.mk' (Function.invFun (rootsRestriction K Ksep m)) sorry

/-- Restricting the inverse selection recovers a finite-level compatible family. -/
theorem rootsRestriction_rootsLift (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (family : TameRoots.limit m.ResidueField (integralClosure.tameRootIndex K m)) :
    rootsRestriction K Ksep m (rootsLift K Ksep m family) = family := sorry

/-- Lifting the restriction recovers a full prime-to-characteristic compatible family. -/
theorem rootsLift_rootsRestriction (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (family : tameRoots Ksep m) :
    rootsLift K Ksep m (rootsRestriction K Ksep m family) = family := sorry

/-- The canonical tame character with values in the full prime-to-characteristic limit in
the residue separable closure. -/
noncomputable def thetaCan (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    m.inertia Gal(Ksep/K) →* tameRoots Ksep m :=
  (rootsLift K Ksep m).comp (integralClosure.thetaCan K m)

/-- Restriction of the full tame character is the finite-level tame character. -/
theorem thetaCan_spec (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    (rootsRestriction K Ksep m).comp (thetaCan K Ksep m) =
      integralClosure.thetaCan K m := sorry

/-- The canonical tame character surjects onto the full prime-to-characteristic limit. -/
theorem thetaCan_surjective (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    Function.Surjective (thetaCan K Ksep m) := sorry

/-- The kernel of the full tame character is profinite wild inertia. -/
theorem thetaCan_ker (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    (thetaCan K Ksep m).ker = profiniteWildInertia K m := sorry

/-- The full tame character intertwines decomposition-group conjugation with the residue
Galois action on every prime-to-characteristic roots-of-unity coordinate. -/
theorem thetaCan_conj (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (τ : MulAction.stabilizer Gal(Ksep/K) m) (σ : m.inertia Gal(Ksep/K))
    (order : primeToIndex A) :
    -- Local instance justification (defeq pin): the roots-of-unity action uses the canonical residue algebra underlying residueGaloisHom.
    letI := integralClosure.ResidueField.algebraOfBase m
    (tameRoots Ksep m).subtype (thetaCan K Ksep m (Ideal.inertiaConjHom m τ σ)) order =
      (residueGaloisHom K Ksep m τ).toMulEquiv.restrictRootsOfUnity order.1
        ((tameRoots Ksep m).subtype (thetaCan K Ksep m σ) order) := sorry

/-- The homomorphism from profinite tame inertia to the full prime-to-characteristic
roots-of-unity limit induced by the canonical tame character. -/
noncomputable def tameQuotientHom (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    profiniteTameInertia K m →* tameRoots Ksep m :=
  QuotientGroup.lift (profiniteWildInertia K m) (thetaCan K Ksep m)
    (thetaCan_ker K Ksep m).symm.le

/-- The tame quotient homomorphism evaluates on an inertia representative as the tame
character. -/
theorem tameQuotientHom_mk (m : Ideal (integralClosure A Ksep)) [m.IsMaximal]
    (σ : m.inertia Gal(Ksep/K)) :
    tameQuotientHom K Ksep m (QuotientGroup.mk σ) = thetaCan K Ksep m σ := sorry

/-- Profinite tame inertia is isomorphic to the full prime-to-characteristic
roots-of-unity limit via the induced tame character. -/
theorem tameQuotientHom_bijective (m : Ideal (integralClosure A Ksep)) [m.IsMaximal] :
    Function.Bijective (tameQuotientHom K Ksep m) := sorry

end integralClosure.SepClosure
