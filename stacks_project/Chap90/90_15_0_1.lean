module

public import stacks_project.Chap90.«90_15_0_1_TangentSpace»

/-!
# Bijective differential of a formal object

The named equation of Stacks Tag 06IM: the differential of the morphism associated to a
formal object of a predeformation category is bijective on tangent spaces.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- 90.15.0.1: the differential `differential ξ : Derivation Λ ξ.base.carrier k → tangentSpace p`
of the morphism associated to a formal object `ξ` of a predeformation category `p` is bijective. -/
@[stacks 06IM]
def BijectiveDifferential (ξ : FormalObject p) [Functor.IsPredeformationCategory p] : Prop :=
  Function.Bijective (differential ξ)

/-- The named equation is bijectivity of `differential ξ`. -/
theorem bijectiveDifferential_iff (ξ : FormalObject p) [Functor.IsPredeformationCategory p] :
    BijectiveDifferential ξ ↔ Function.Bijective (differential ξ) := sorry

end FormalObject
