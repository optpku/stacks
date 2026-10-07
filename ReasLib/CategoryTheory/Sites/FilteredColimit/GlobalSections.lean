module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf
import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered colimits and global sections on a site

This file owns the quasi-compact test-set criterion ensuring that global sections commute with
filtered colimits.  It is independent of module sheaves and textbook chapter facades.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable {I : Type w} [Category.{max u v} I]

/-- A quasi-compact test set lifts locally surjective maps to the terminal sheaf through one of
its elements, and each member has quasi-compact self-product. -/
@[mk_iff isQuasiCompactTestSet_iff]
class IsQuasiCompactTestSet (S : Set (Sheaf J (Type (max u v)))) : Prop where
  /-- A locally surjective map to the terminal sheaf can be tested after a locally surjective
  map from one member of the test set. -/
  lift_terminal
      {F : Sheaf J (Type (max u v))}
      (hF : IsLocallySurjective (terminal.from F)) :
      ∃ K : Sheaf J (Type (max u v)), K ∈ S ∧ ∃ κ : K ⟶ F,
        IsLocallySurjective (κ ≫ terminal.from F)
  /-- The self-product of every member of the test set is quasi-compact. -/
  quasiCompact_selfProduct
      {K : Sheaf J (Type (max u v))} (hK : K ∈ S) :
      (K ⨯ K).IsQuasiCompactObject

namespace QuasiCompact

/-- The site-level hypothesis that there is a quasi-compact test set for global sections. -/
@[stacks 0GMR "test-set hypothesis"]
class HasTestSet : Prop where
  /-- A set of sheaves satisfying the quasi-compact test-set criterion. -/
  exists_testSet :
    ∃ S : Set (Sheaf J (Type (max u v))), IsQuasiCompactTestSet J S

end QuasiCompact

namespace Sheaf.FilteredColimit
namespace GlobalSections

/-- The canonical comparison from the filtered colimit of global sections to the global
sections of the colimit sheaf. -/
noncomputable abbrev comparison
    (F : I ⥤ Sheaf J (Type (max u v)))
    [HasColimit F]
    [HasColimit (F ⋙ Sheaf.Γ J (Type (max u v)))] :=
  colimit.post F (Sheaf.Γ J (Type (max u v)))

/-- The comparison agrees with the global-sections image of each colimit inclusion. -/
@[reassoc (attr := simp)]
theorem ι_comparison
    (F : I ⥤ Sheaf J (Type (max u v)))
    [HasColimit F]
    [HasColimit (F ⋙ Sheaf.Γ J (Type (max u v)))] (i : I) :
    colimit.ι (F ⋙ Sheaf.Γ J (Type (max u v))) i ≫ comparison J F =
      (Sheaf.Γ J (Type (max u v))).map (colimit.ι F i) := sorry

variable [Small.{max u v} I] [IsFiltered I]

/-- Lemma 7.17.8 (0GMR) (1): monic transitions make the global-sections comparison
injective. -/
@[stacks 0GMR "(1)"]
theorem injective_of_transitionMono
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    Function.Injective (comparison J F) := sorry

/-- Lemma 7.17.8 (0GMR) (2): quasi-compactness of the terminal sheaf makes the
global-sections comparison injective. -/
@[stacks 0GMR "(2)"]
theorem injective_of_quasiCompact
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hJ : (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject) :
    Function.Injective (comparison J F) := sorry

/-- Lemma 7.17.8 (0GMR) (3): with a quasi-compact terminal sheaf and monic transitions, the
global-sections comparison is an isomorphism. -/
@[stacks 0GMR "(3)"]
theorem isIso_of_quasiCompact_of_transitionMono
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hJ : (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject)
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    IsIso (comparison J F) := sorry

/-- Lemma 7.17.8 (0GMR) (4): a quasi-compact test set makes the global-sections comparison
bijective for every filtered diagram of set-valued sheaves. -/
@[stacks 0GMR "(4), bijective"]
theorem bijective_of_testSet
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hS : QuasiCompact.HasTestSet J) :
    Function.Bijective (comparison J F) := sorry

/-- The typeclass-friendly isomorphism form of the quasi-compact test-set criterion. -/
@[stacks 0GMR "(4), isomorphism"]
theorem isIso_of_testSet
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hS : QuasiCompact.HasTestSet J) :
    IsIso (comparison J F) := sorry

/-- A quasi-compact test set ensures that global sections of set-valued sheaves preserve
filtered colimits.  The test-set class is the only additional site-specific input beyond the
ambient sheaf-category assumptions. -/
instance preservesFilteredColimits [QuasiCompact.HasTestSet J] :
    PreservesFilteredColimits (Sheaf.Γ J (Type (max u v))) := sorry

end GlobalSections
end Sheaf.FilteredColimit

section InstanceSynthesis

variable [QuasiCompact.HasTestSet J]

#synth PreservesFilteredColimits (Sheaf.Γ J (Type (max u v)))

end InstanceSynthesis

/- Data and axiom audit (mathlib 4.32): `GlobalSections.comparison` is the canonical
`colimit.post` morphism and introduces no selected witness or deferred proof field. -/

end CategoryTheory.GrothendieckTopology
