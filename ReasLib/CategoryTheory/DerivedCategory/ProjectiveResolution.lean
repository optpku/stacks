module

public import ReasLib.Algebra.Homology.HomotopyCategory.Termwise.BoundedAbove
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.HomotopyCategory.Minus.Projective

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical comparison functor from the bounded-above homotopy category of
termwise-projective complexes to the bounded-above derived category. -/
noncomputable abbrev toDerived :
    HomotopyCategory.Minus.TermsIn 𝒜 (isProjective 𝒜) ⥤ DerivedCategory.Minus 𝒜 :=
  ObjectProperty.ι (HomotopyCategory.Minus.termsIn 𝒜 (isProjective 𝒜)) ⋙
    DerivedCategory.Minus.Qh 𝒜

namespace toDerived

variable {𝒜}

/-- If an abelian category has enough projectives, the canonical comparison from
bounded-above termwise-projective homotopy objects to its bounded-above derived category
is an equivalence. -/
instance isEquivalence [EnoughProjectives 𝒜] :
    (Projective.toDerived 𝒜).IsEquivalence := sorry

end toDerived

end CategoryTheory.HomotopyCategory.Minus.Projective
