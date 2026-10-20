module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying.Limit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Milnor cohomology rows for objectwise derived sections

This leaf combines the derived-limit preservation of objectwise module sections with the generic
Milnor short exact sequence.  The cohomology tower is the canonical `Underlying.cohomologyTower`;
there is no chapter-specific alias or locally rebuilt inverse system.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections.Underlying

variable (X : RingedSite.{u, v, w})

/-- Lemma 21.23.2 (0D6K): the objectwise cohomology of a sequential derived limit fits into the
Milnor short exact sequence.  The left term is the canonical `firstDerivedLimit` of the
degree-`m - 1` cohomology tower. -/
@[stacks 0D6K "Milnor short exact sequence for objectwise derived sections"]
theorem cohomologyShortExact
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]
    (U : X)
    (Ksys : SequentialInverseSystem (ModuleDerived.{z} X))
    (K : ModuleDerived.{z} X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι : (cohomologyTower X U Ksys (m - 1)).firstDerivedLimit ⟶
        RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U K m)
      (π : RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U K m ⟶
        limit (cohomologyTower X U Ksys m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end RingedSite.Hom.ModuleSections.Underlying

end
