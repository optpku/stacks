module

public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries

/-!
# Minimal versal formal objects

A predeformation category with a versal formal object admits a minimal versal
formal object, unique up to isomorphism; every versal object is the pushforward
of a minimal versal object along a power series ring extension.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op [Functor.IsPredeformationCategory p] :
    Functor.IsFibered.InGroupoids p.op :=
  Functor.IsPredeformationCategory.isCofiberedInGroupoids

/-- Lemma 90.14.5 (1): if `p` is a predeformation category and `ξ` is a versal
formal object of `p`, then `p` has a minimal versal formal object. -/
@[stacks 06T5]
theorem exists_isMinimalVersal [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ ξ' : FormalObject p, IsMinimalVersal ξ' :=
  sorry

/-- Lemma 90.14.5 (2): if `p` is a predeformation category, then any two minimal
versal formal objects of `p` are isomorphic. -/
@[stacks 06T5]
theorem nonempty_iso [Functor.IsPredeformationCategory p]
    (ξ η : FormalObject p) [IsMinimalVersal ξ] [IsMinimalVersal η] :
    Nonempty (ξ ≅ η) :=
  sorry

/-- Lemma 90.14.5 (3): if `p` is a predeformation category and `ξ` is a versal
formal object of `p`, then `ξ` is the pushforward of a minimal versal formal
object `ξ'` along a power series ring extension, realized by a morphism
`f : ξ' ⟶ ξ` with `IsPowerSeriesOver f.base`. -/
@[stacks 06T5]
theorem exists_isPowerSeriesOver [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ),
      IsMinimalVersal ξ' ∧ IsPowerSeriesOver f.base :=
  sorry

/-- Every morphism of formal objects between minimal versal objects is an
isomorphism. -/
instance isIso [Functor.IsPredeformationCategory p]
    {ξ η : FormalObject p} [IsMinimalVersal ξ] [IsMinimalVersal η]
    (f : ξ ⟶ η) : IsIso f :=
  sorry

end FormalObject
