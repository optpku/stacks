module

public import stacks_project.Chap90.«90_15_0_2»
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Versal formal objects satisfying 90.15.0.2

A versal formal object of a predeformation category whose differential is
bijective on `Derivation Λ k k`-orbits is minimal versal, hence unique up to
isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- Lemma 90.15.1 (1): if `p` is a predeformation category and `ξ` is a versal
formal object of `p` such that `BijectiveDifferentialOnOrbits ξ` holds, then `ξ`
is a minimal versal formal object. -/
@[stacks 06IR, reducible]
def instIsMinimalVersal_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [IsVersal ξ]
    (h : BijectiveDifferentialOnOrbits ξ) : IsMinimalVersal ξ := sorry

/-- Lemma 90.15.1 (2): if `p` is a predeformation category, then any two versal
formal objects of `p` satisfying `BijectiveDifferentialOnOrbits` are isomorphic. -/
@[stacks 06IR]
theorem nonempty_iso_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ η : FormalObject p)
    [IsVersal ξ] [IsVersal η] (hξ : BijectiveDifferentialOnOrbits ξ)
    (hη : BijectiveDifferentialOnOrbits η) : Nonempty (ξ ≅ η) := sorry

end FormalObject
