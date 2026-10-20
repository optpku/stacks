module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Injective Objects as Right-Acyclic Objects

This leaf specializes bounded-below K-injective computation to degree-zero
complexes. It supplies both the bounded-below and unbounded acyclicity forms,
without requiring a global choice of injective resolutions.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section BoundedBelow

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-- Stacks 05TH: an injective object computes the bounded-below right-derived
functor of every additive functor. -/
@[stacks 05TH]
theorem RightAcyclic.Bounded.of_injective
    (I : 𝒜) [Injective I] :
    RightAcyclic.Bounded F I := sorry

/-- If the source category has enough injectives, bounded-below right-acyclic objects for an
additive functor admit monomorphic embeddings. -/
@[stacks 05TH]
instance RightAcyclic.Bounded.hasMonoEmbedding [EnoughInjectives 𝒜] :
    ObjectProperty.HasMonoEmbedding (RightAcyclic.Bounded F) := sorry

end BoundedBelow

section Unbounded

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-- Stacks 05TH: an injective object computes the unbounded right-derived
functor of every additive functor. -/
@[stacks 05TH]
theorem RightAcyclic.of_injective
    (I : 𝒜) [Injective I] :
    RightAcyclic F I := sorry

/-- If the source category has enough injectives, right-acyclic objects for an additive functor
admit monomorphic embeddings. -/
instance RightAcyclic.hasMonoEmbedding [EnoughInjectives 𝒜] :
    ObjectProperty.HasMonoEmbedding (RightAcyclic F) := sorry

end Unbounded


end CategoryTheory.Functor
