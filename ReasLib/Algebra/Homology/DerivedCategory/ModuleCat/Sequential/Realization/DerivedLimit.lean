module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.DerivedLimit
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Realization
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology

/-!
# Derived inverse limits of realized module towers

A realization of a varying-ring derived module tower has a derived inverse limit over the inverse
limit ring.  This object is a derived limit of the tower after restriction to that fixed base, so
its isomorphism class and Milnor cohomology sequence depend only on the tower.

@stack 07KZ
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower

-- Local instance justification (defeq pin): the comparison uses the standard derived categories
-- on the varying-ring module category and on modules over the inverse-limit ring.
attribute [local instance] HasDerivedCategory.standard

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

namespace Realization

/-- Remark 15.88.6 (1): the derived inverse limit of a realization is a derived limit of the
prescribed tower after restricting every stage to the inverse-limit ring. -/
@[stacks 07KZ "(1), a realization computes the derived limit"]
theorem isDerivedLimit
    {T : DerivedTower (SequentialInverseSystem.sequentialRingSystem A ρ)}
    {K : DerivedCategory (SequentialInverseSystem.SeqRingMod.{u, u} A ρ)}
    (hK : T.Realization K) :
    Nonempty (CategoryTheory.IsDerivedLimit
      (T.restrict
        (getLimitCone (SequentialInverseSystem.sequentialRingSystem A ρ)).cone)
      ((ringedModuleDerivedInverseLimitFunctor A ρ).obj K)) := sorry

/-- Remark 15.88.6 (2): the derived inverse limits of any two realizations of the same tower are
isomorphic over the inverse-limit ring. -/
@[stacks 07KZ "(2), independence of the realization"]
theorem derivedInverseLimitIsomorphic
    {T : DerivedTower (SequentialInverseSystem.sequentialRingSystem A ρ)}
    {K L : DerivedCategory (SequentialInverseSystem.SeqRingMod.{u, u} A ρ)}
    (hK : T.Realization K) (hL : T.Realization L) :
    IsIsomorphic
      ((ringedModuleDerivedInverseLimitFunctor A ρ).obj K)
      ((ringedModuleDerivedInverseLimitFunctor A ρ).obj L) := sorry

/-- Remark 15.88.6 (3): every realization has the Milnor short exact sequence relating the
cohomology of its derived inverse limit to `lim` and `R¹ lim` of the stage cohomology. -/
@[stacks 07KZ "(3), Milnor cohomology short exact sequence"]
theorem cohomologyShortExact
    {T : DerivedTower (SequentialInverseSystem.sequentialRingSystem A ρ)}
    {K : DerivedCategory (SequentialInverseSystem.SeqRingMod.{u, u} A ρ)}
    (hK : T.Realization K) (p : ℤ) :
    ∃ (ι : CategoryTheory.DerivedLimit.R1
        (T.restrict
          (getLimitCone (SequentialInverseSystem.sequentialRingSystem A ρ)).cone ⋙
            DerivedCategory.homologyFunctor
              (limitModule A ρ) (p - 1)) ⟶
        (DerivedCategory.homologyFunctor
          (limitModule A ρ) p).obj
            ((ringedModuleDerivedInverseLimitFunctor A ρ).obj K))
      (π : (DerivedCategory.homologyFunctor
          (limitModule A ρ) p).obj
            ((ringedModuleDerivedInverseLimitFunctor A ρ).obj K) ⟶
        limit (T.restrict
          (getLimitCone (SequentialInverseSystem.sequentialRingSystem A ρ)).cone ⋙
            DerivedCategory.homologyFunctor
              (limitModule A ρ) p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end Realization

end CategoryTheory.ModuleCat.DerivedTower
