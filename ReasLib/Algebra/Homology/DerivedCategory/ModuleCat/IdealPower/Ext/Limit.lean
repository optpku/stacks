module

public import Mathlib.CategoryTheory.Filtered.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Presentation
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of Ext over Ideal-Power Quotients

This file packages the sequential system `Ext^i_A(K, M / I^(n+1)M)` and its essential constancy
under a uniform ideal-power torsion hypothesis on higher Ext modules.

@stack 0DYJ
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory.Ext Opposite

universe u

-- Local instance justification (instance diamond): use the standard derived-category model only
-- for this ideal-power Ext limit comparison.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.IdealPower.ExtQuotient

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The sequential inverse system `Ext^i_A(K, M / I^(n+1)M)`, indexed from `n = 0`. -/
@[stacks 0DYJ "Ext tower over positive ideal-power quotients"]
abbrev positiveTower (I : Ideal A) (K : DerivedCategory (ModuleCat A))
    (M : ModuleCat A) (i : ℤ) : SequentialInverseSystem (ModuleCat A) :=
  Ideal.PowerQuotient.positiveSystem I M ⋙ moduleFunctor K i

/-- All Ext modules in degrees at least `a`, against finite modules, are `I`-power torsion. -/
@[stacks 0DYJ "uniform ideal-power torsion of higher Ext"]
def IsPowerTorsionAbove (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (a : ℤ) : Prop :=
  ∀ (N : ModuleCat.{u} A), Module.Finite A N → ∀ ⦃j : ℤ⦄, a ≤ j →
    Module.IsIdealPowerTorsion I ((moduleFunctor K j).obj N)

/-- Lemma 15.103.1: the Ext tower over positive ideal-power quotients is essentially constant
with value `Ext^i_A(K, M)`. -/
@[stacks 0DYJ "essential constancy of Ext over ideal-power quotients"]
theorem exists_essentiallyConstantCone
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (hK : K.IsPseudoCoherent) (a : ℤ)
    (hExt : IsPowerTorsionAbove I K a) (i : ℤ) (hi : a ≤ i)
    (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : Cone (positiveTower I K M i),
      c.pt = (moduleFunctor K i).obj M ∧ c.IsEssentiallyConstant := sorry

/-- The essentially constant Ext tower admits a limit cone with vertex `Ext^i_A(K, M)`. -/
@[stacks 0DYJ "limit of Ext over ideal-power quotients"]
theorem exists_limitCone
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (hK : K.IsPseudoCoherent) (a : ℤ)
    (hExt : IsPowerTorsionAbove I K a) (i : ℤ) (hi : a ≤ i)
    (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : LimitCone (positiveTower I K M i),
      c.cone.pt = (moduleFunctor K i).obj M ∧ c.cone.IsEssentiallyConstant := sorry

end CategoryTheory.DerivedCategory.IdealPower.ExtQuotient
