/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.«90_15_0_2_Action»

/-!
# Bijective differential on Derivation Λ k k-orbits

The named equation of Stacks Tag 06T6: the differential of the morphism associated to a
formal object of a predeformation category is bijective on `Derivation Λ k k`-orbits.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- 90.15.0.2: the differential `differential ξ : Derivation Λ ξ.base.carrier k → tangentSpace p`
of the morphism associated to a formal object `ξ` of a predeformation category `p` is bijective
on `Derivation Λ k k`-orbits. -/
@[stacks 06T6]
def BijectiveDifferentialOnOrbits (ξ : FormalObject p) [Functor.IsPredeformationCategory p] :
    Prop :=
  (∀ y, ∃ D, y ∈ AddAction.orbit (Derivation Λ k k) (differential ξ D)) ∧
    (∀ D₁ D₂,
      differential ξ D₁ ∈ AddAction.orbit (Derivation Λ k k) (differential ξ D₂) ↔
        D₁ ∈ AddAction.orbit (Derivation Λ k k) D₂)

/-- The named equation is orbit-surjectivity and orbit-injectivity of `differential ξ`. -/
theorem bijectiveDifferentialOnOrbits_iff (ξ : FormalObject p)
    [Functor.IsPredeformationCategory p] :
    BijectiveDifferentialOnOrbits ξ ↔
      (∀ y, ∃ D, y ∈ AddAction.orbit (Derivation Λ k k) (differential ξ D)) ∧
        (∀ D₁ D₂,
          differential ξ D₁ ∈ AddAction.orbit (Derivation Λ k k) (differential ξ D₂) ↔
            D₁ ∈ AddAction.orbit (Derivation Λ k k) D₂) := sorry

end FormalObject
