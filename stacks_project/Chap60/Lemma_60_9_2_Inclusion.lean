module

import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Definition_60_9_1
public import stacks_project.Chap60.Definition_60_8_4
public import stacks_project.Chap60.Lemma_60_8_2
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/-- The inclusion functor `Cris(X/S) ⥤ CRIS(X/S)`. -/
abbrev smallCrystallineInclusion :
    smallCrystallineSite S I γ h_compatible X x₀ ⥤
      RelativeCRIS S I γ h_compatible X x₀ :=
  (smallCrystallineProperty S I γ h_compatible X x₀).ι

/-- The inclusion of the small crystalline site is the object-property inclusion. -/
theorem smallCrystallineInclusion_def :
    smallCrystallineInclusion S I γ h_compatible X x₀ =
      (smallCrystallineProperty S I γ h_compatible X x₀).ι := sorry

/-- The small crystalline site has all finite nonempty limits. -/
instance smallCrystallineSite_hasFiniteNonemptyLimits :
    HasFiniteNonemptyLimits (smallCrystallineSite S I γ h_compatible X x₀) := sorry

/-- The inclusion `Cris(X/S) ⥤ CRIS(X/S)` preserves finite nonempty limits. -/
instance smallCrystallineInclusion_preservesFiniteNonemptyLimits :
    PreservesFiniteNonemptyLimits
      (smallCrystallineInclusion S I γ h_compatible X x₀) := sorry

/-- The inclusion `Cris(X/S) ⥤ CRIS(X/S)` is fully faithful. -/
def smallCrystallineInclusion_fullyFaithful :
    (smallCrystallineInclusion S I γ h_compatible X x₀).FullyFaithful :=
  (smallCrystallineProperty S I γ h_compatible X x₀).fullyFaithfulι

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The inclusion is continuous for the Zariski crystalline topologies. -/
instance smallCrystallineInclusion_isContinuous :
    Functor.IsContinuous
      (smallCrystallineInclusion S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

/-- The inclusion is cocontinuous for the Zariski crystalline topologies. -/
instance smallCrystallineInclusion_isCocontinuous :
    Functor.IsCocontinuous
      (smallCrystallineInclusion S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

end AlgebraicGeometry.Scheme.Crystalline
