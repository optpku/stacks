module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksCheckRecall

@[expose] public section

/- 20.3.0.2: the `i`-th right derived functor is the composite of a chosen derived functor with
the degree-`i` homology functor. -/

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Abelian ℬ] [HasDerivedCategory ℬ]

@[stacks 05U4 "higher right derived functors as derived homology"]
#check fun (RF : 𝒜 ⥤ DerivedCategory ℬ) (i : ℤ) =>
  RF ⋙ DerivedCategory.homologyFunctor ℬ i

end

end
