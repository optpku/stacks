/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coverwise local bijectivity of presheaf maps

This module records the concrete presentation in which every object has a
covering family on whose members a map of set-valued presheaves is bijective.
It is a convenient sufficient criterion for Mathlib's sieve-based local
injectivity, local surjectivity, and `GrothendieckTopology.W` predicates.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

universe v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {F G : Cᵒᵖ ⥤ Type (max u v)} (η : F ⟶ G)

/-- `η` is componentwise bijective on a covering family over every object of `C`. -/
def HasCoverByBijective : Prop :=
  ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
    Sieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ J U ∧
      ∀ i : families.index, Function.Bijective (η.app (op (families.obj i).left))

namespace HasCoverByBijective

variable {J η}

/-- A coverwise-bijective presheaf map gives enough objects for the object property on which
its components are bijective. -/
theorem hasEnoughObjects (hη : HasCoverByBijective J η) :
    J.HasEnoughObjectsWithProperty
      (fun U => Function.Bijective (η.app (op U))) := sorry

/-- Coverwise componentwise bijectivity is precisely the existing enough-objects predicate for
the object property on which the components of `η` are bijective. -/
theorem iff_hasEnoughObjects :
    HasCoverByBijective J η ↔
      J.HasEnoughObjectsWithProperty
        (fun U => Function.Bijective (η.app (op U))) := sorry

/-- A coverwise-bijective presheaf map is locally injective. -/
theorem isLocallyInjective (hη : HasCoverByBijective J η) :
    IsLocallyInjective J η := sorry

/-- A coverwise-bijective presheaf map is locally surjective. -/
theorem isLocallySurjective (hη : HasCoverByBijective J η) :
    IsLocallySurjective J η := sorry

/-- A coverwise-bijective presheaf map is locally bijective in the canonical pair of senses. -/
theorem isLocallyBijective (hη : HasCoverByBijective J η) :
    IsLocallyInjective J η ∧ IsLocallySurjective J η := sorry

/-- A coverwise-bijective presheaf map belongs to the sheafification equivalence class `J.W`. -/
theorem w (hη : HasCoverByBijective J η) : J.W η := sorry

end HasCoverByBijective

end CategoryTheory.Presheaf
