module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
import StacksCheckRecall

/-!
# Definition 15.70.1

@stack 0A5S
-/

@[expose] public section

/-!
# Definition 15.70.1: finite injective dimension

The reusable definitions are object properties on an arbitrary derived category.  The source
specialization to `DerivedCategory (ModuleCat R)` is obtained by inference.
-/

/- Definition 15.70.1 (1), tag `0A5S`: finite injective dimension. -/
@[stacks 0A5S "(1), finite injective dimension"]
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension

/- Definition 15.70.1 (2), tag `0A5S`: injective amplitude in a fixed interval. -/
@[stacks 0A5S "(2), injective amplitude"]
#check @CategoryTheory.DerivedCategory.HasInjectiveAmplitudeIn

/- The bundled bounded-injective representative used by the canonical property. -/
#check @CochainComplex.InjectiveIn

/- The compatibility spelling used by existing Chapter 15 consumers. -/
#check @CategoryTheory.HasFiniteInjectiveDimension

/- Module-level finite injective dimension remains the canonical Mathlib invariant. -/
#check CategoryTheory.injectiveDimension
#check CategoryTheory.injectiveDimension_ne_top_iff
#check CategoryTheory.injectiveDimension_le_iff
