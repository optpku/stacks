module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Presentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties

/-!
# Cover Criteria for Local Properties of Sheaves of Modules

These criteria use `GrothendieckTopology.CoversTop`, so no chosen terminal
object is exposed in the API.  The statements are valid for an arbitrary
sheaf of rings and split each source equivalence into independently reusable
local and global forms.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace IsLocallyFree

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Local freeness can be checked after restriction to the members of one cover of the top. -/
@[stacks 03DN "(1, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) :
    M.IsLocallyFree ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, (M.over (X i)).IsLocallyFree := sorry

end Local

/-- Local freeness is equivalent to freeness on the members of one cover of the top. -/
@[stacks 03DN "(1, free)"]
theorem iff_existsFreeCover
    (M : SheafOfModules.{w} R) :
    M.IsLocallyFree ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFree (M.over (X i)) := sorry

end IsLocallyFree

namespace IsFiniteLocallyFree

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finite local freeness can be checked after restriction to the members of one cover of the
top. -/
@[stacks 03DN "(2, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) :
    IsFiniteLocallyFree M ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, IsFiniteLocallyFree (M.over (X i)) := sorry

end Local

/-- Finite local freeness is equivalent to finite freeness on the members of one cover of the
top. -/
@[stacks 03DN "(2, finite free)"]
theorem iff_existsFiniteFreeCover
    (M : SheafOfModules.{w} R) :
    IsFiniteLocallyFree M ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFiniteFree (M.over (X i)) := sorry

end IsFiniteLocallyFree

namespace IsLocallyGeneratedBySections

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Local generation can be checked after restriction to the members of one cover of the top. -/
@[stacks 03DN "(3, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) :
    IsLocallyGeneratedBySections M ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, IsLocallyGeneratedBySections (M.over (X i)) := sorry

end Local

/-- Local generation is equivalent to global generation on the members of one cover of the
top. -/
@[stacks 03DN "(3, global)"]
theorem iff_existsGloballyGeneratedCover
    (M : SheafOfModules.{w} R) :
    IsLocallyGeneratedBySections M ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsGloballyGenerated (M.over (X i)) := sorry

end IsLocallyGeneratedBySections

namespace IsLocallyGeneratedBy

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Local generation by `r` sections can be checked after restriction to the members of one
cover of the top. -/
@[stacks 03DN "(4, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) (r : ℕ) :
    IsLocallyGeneratedBy M r ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, IsLocallyGeneratedBy (M.over (X i)) r := sorry

end Local

/-- Local generation by `r` sections is equivalent to generation by `r` global sections on the
members of one cover of the top. -/
@[stacks 03DN "(4, global)"]
theorem iff_existsGeneratedByCover
    (M : SheafOfModules.{w} R) (r : ℕ) :
    IsLocallyGeneratedBy M r ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsGeneratedBy (M.over (X i)) r := sorry

end IsLocallyGeneratedBy

namespace IsFiniteType

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finite type can be checked after restriction to the members of one cover of the top. -/
@[stacks 03DN "(5, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) :
    M.IsFiniteType ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, (M.over (X i)).IsFiniteType := sorry

end Local

/-- Finite type is equivalent to finite global generation on the members of one cover of the
top. -/
@[stacks 03DN "(5, global)"]
theorem iff_existsFiniteGloballyGeneratedCover
    (M : SheafOfModules.{w} R) :
    M.IsFiniteType ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFiniteGloballyGenerated (M.over (X i)) := sorry

end IsFiniteType

namespace IsQuasicoherent

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Quasi-coherence can be checked after restriction to the members of one cover of the top. -/
@[stacks 03DN "(6, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) :
    M.IsQuasicoherent ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, (M.over (X i)).IsQuasicoherent := sorry

end Local

/-- Quasi-coherence is equivalent to a global presentation on every member of one cover of the
top. -/
@[stacks 03DN "(6, presentation)"]
theorem iff_existsPresentationCover
    (M : SheafOfModules.{w} R) :
    M.IsQuasicoherent ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.HasGlobalPresentation (M.over (X i)) := sorry

end IsQuasicoherent

namespace IsFinitePresentation

section Local

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finite presentation can be checked after restriction to the members of one cover of the
top. -/
@[stacks 03DN "(7, local)"]
theorem iff_existsCover
    (M : SheafOfModules.{w} R) :
    M.IsFinitePresentation ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, (M.over (X i)).IsFinitePresentation := sorry

end Local

/-- Finite presentation is equivalent to a finite global presentation on every member of one
cover of the top. -/
@[stacks 03DN "(7, presentation)"]
theorem iff_existsFinitePresentationCover
    (M : SheafOfModules.{w} R) :
    M.IsFinitePresentation ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.HasFiniteGlobalPresentation (M.over (X i)) := sorry

end IsFinitePresentation

section Coherence

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U, ∀ W : Over V,
  HasWeakSheafify (((J.over U).over V).over W) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U, ∀ W : Over V,
  (((J.over U).over V).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Coherence can be checked after restriction to the members of one cover of the top. -/
@[stacks 03DN "(8)"]
theorem IsCoherent.iff_existsCover
    (M : SheafOfModules.{w} R) :
    IsCoherent M ↔
      ∃ (I : Type u) (X : I → C), J.CoversTop X ∧
        ∀ i : I, IsCoherent (M.over (X i)) := sorry

end Coherence

end SheafOfModules.RingedSite
