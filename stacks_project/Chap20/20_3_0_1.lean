module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
import StacksCheckRecall

@[expose] public section

/-!
# 20.3.0.1

The bounded-below derived category is the canonical `t.plus` full
subcategory, and resolution-lift calculations are owned by the generic
functorial-injective-resolution localization API.  This file deliberately
contains no chapter-local derived-category instance or resolution notation.
-/

open CategoryTheory
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v u

section

variable {X : Type u} [Category.{v} X] [Abelian X] [HasDerivedCategory.{w} X]

/- 20.3.0.1 (1): `D⁺(X)` is the full subcategory cut out by `t.plus`; membership
means vanishing cohomology in all sufficiently low degrees. -/
@[stacks 013V] #check @DerivedCategory.plus_iff

#check (t.plus : ObjectProperty (DerivedCategory X))
#check (D⁺(X) : Type _)

end

/- 20.3.0.1 (2): after a functorial injective resolution is lifted through a
quasi-isomorphism localization, every right derived functor is canonically
isomorphic to evaluation on the lifted injective representative. -/
@[stacks 05TN] #check
  @HomotopyCategory.Plus.InjectiveResolutionFunctor.isIsomorphic_rightDerived_lift

#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.liftComparison
#check @Functor.rightDerivedUnique

end
