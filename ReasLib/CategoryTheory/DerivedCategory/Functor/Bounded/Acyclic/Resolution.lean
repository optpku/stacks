module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Basic
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Acyclicity from Resolution Classes

This module supplies source-independent criteria making the members of a resolution class
acyclic for bounded derived functors. The class is expressed using the canonical object-property
cover conditions, rather than a chapter-specific resolution package.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-- Stacks 05T8: if every object embeds into a member of `P`, `P` is closed under the indicated
cokernel operation, and `F` preserves the resulting short exact sequences, then every member of
`P` is bounded-below right acyclic for `F`. The closure and exactness hypotheses are separate so
that standard object-property instances can be reused independently. -/
@[stacks 05T8]
theorem RightAcyclic.Bounded.of_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    (h_mem : ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (h_map : ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ →
      (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    RightAcyclic.Bounded F A := sorry

/-- A quotient-generating class closed under subobjects supplies bounded-above left-acyclic
objects for an additive functor when the functor preserves the indicated short exact sequences. -/
theorem LeftAcyclic.Bounded.of_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (h_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    LeftAcyclic.Bounded F A := sorry

/-- Stacks 05T9: under the quotient-generating and short-exact hypotheses, every member of `P`
is left acyclic for the unbounded derived functor of `F`. -/
@[stacks 05T9]
theorem LeftAcyclic.of_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (h_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    LeftAcyclic F A := sorry

end

end CategoryTheory.Functor
