module

public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.Sheaf.Types.Colimits
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentations by sheafified representables

This module turns a cover-by-property hypothesis into the standard coequalizer presentation of a
sheaf by coproducts of sheafified representables.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open Opposite

noncomputable section

universe w u v

namespace CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A sieve-saturated cover-by-property hypothesis gives a locally surjective map to a sheaf from
a coproduct of sheafified representables attached to objects satisfying that property. -/
@[stacks 093B "(1), sieve-saturated specialization"]
theorem existsSheafifiedRepresentableCover
    {E : ObjectProperty C} (hE : J.HasEnoughObjectsWithProperty E)
    (F : Sheaf J (Type (max w u v))) :
    ∃ U : Limits.FormalCoproduct.{max w u v} C,
      (∀ i : U.index, E (U.obj i)) ∧
        ∃ π : (∐ fun i : U.index ↦ J.uliftSheafifiedRepresentable.{w} (U.obj i)) ⟶ F,
          Sheaf.IsLocallySurjective π := sorry

/-- Lemma 7.12.5: if every object is covered by objects of `E`, every sheaf of sets has a
coequalizer presentation by coproducts of sheafified representables attached to objects of `E`. -/
@[stacks 00WS "sieve-saturated specialization"]
theorem existsCoequalizerPresentation
    {E : ObjectProperty C} (hE : J.HasEnoughObjectsWithProperty E)
    (F : Sheaf J (Type (max w u v))) :
    ∃ U₀ U₁ : Limits.FormalCoproduct.{max w u v} C,
      (∀ i : U₀.index, E (U₀.obj i)) ∧
      (∀ i : U₁.index, E (U₁.obj i)) ∧
        ∃ (p q :
            (∐ fun i : U₁.index ↦ J.uliftSheafifiedRepresentable.{w} (U₁.obj i)) ⟶
              (∐ fun i : U₀.index ↦ J.uliftSheafifiedRepresentable.{w} (U₀.obj i)))
          (π : (∐ fun i : U₀.index ↦ J.uliftSheafifiedRepresentable.{w} (U₀.obj i)) ⟶ F)
          (hπ : p ≫ π = q ≫ π),
          Nonempty (IsColimit (Cofork.ofπ π hπ)) := sorry

end CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty

namespace CategoryTheory.Coverage.HasEnoughObjectsWithProperty

variable {C : Type u} [Category.{v} C] {K : Coverage C}

/-- Lemma 18.30.6 (093B) (1): enough objects for a chosen coverage give a locally surjective map
from a coproduct of sheafified representables to every sheaf of sets. -/
@[stacks 093B "(1)"]
theorem existsSheafifiedRepresentableCover
    {E : ObjectProperty C} (hE : K.HasEnoughObjectsWithProperty E)
    (F : Sheaf K.toGrothendieck (Type (max w u v))) :
    ∃ U : Limits.FormalCoproduct.{max w u v} C,
      (∀ i : U.index, E (U.obj i)) ∧
        ∃ π : (∐ fun i : U.index ↦
            K.toGrothendieck.uliftSheafifiedRepresentable.{w} (U.obj i)) ⟶ F,
          Sheaf.IsLocallySurjective π := sorry

/-- Lemma 7.12.5 (00WS): enough objects for a chosen coverage give a coequalizer presentation
of every sheaf of sets by coproducts of sheafified representables. -/
@[stacks 00WS]
theorem existsCoequalizerPresentation
    {E : ObjectProperty C} (hE : K.HasEnoughObjectsWithProperty E)
    (F : Sheaf K.toGrothendieck (Type (max w u v))) :
    ∃ U₀ U₁ : Limits.FormalCoproduct.{max w u v} C,
      (∀ i : U₀.index, E (U₀.obj i)) ∧
      (∀ i : U₁.index, E (U₁.obj i)) ∧
        ∃ (p q :
            (∐ fun i : U₁.index ↦
                K.toGrothendieck.uliftSheafifiedRepresentable.{w} (U₁.obj i)) ⟶
              (∐ fun i : U₀.index ↦
                K.toGrothendieck.uliftSheafifiedRepresentable.{w} (U₀.obj i)))
          (π : (∐ fun i : U₀.index ↦
              K.toGrothendieck.uliftSheafifiedRepresentable.{w} (U₀.obj i)) ⟶ F)
          (hπ : p ≫ π = q ≫ π),
          Nonempty (IsColimit (Cofork.ofπ π hπ)) := sorry

end CategoryTheory.Coverage.HasEnoughObjectsWithProperty
