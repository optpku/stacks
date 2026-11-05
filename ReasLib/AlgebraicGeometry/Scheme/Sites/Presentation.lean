/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Containment of chosen big-site presentations

Seed extension is separate from containment of the entire site. Actual
containment records a comparison functor over schemes that preserves every
covering family. Common extensions do not shrink the object universe.
The source-facing version uses the existing `SchAlphaBigSite` model.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigSite

variable {P : Precoverage Scheme.{u}}

/-- The ambient schemes represented by the selected objects of a chosen big-site
presentation. -/
def seedSchemesImage (X : ChosenBigSite.{u, v} P) : Set Scheme.{u} :=
  X.toScheme.obj '' X.seedSchemes

/-- Membership in the ambient image of the selected objects of a chosen
big-site presentation. -/
theorem mem_seedSchemesImage_iff (X : ChosenBigSite.{u, v} P) (T : Scheme.{u}) :
    T ∈ seedSchemesImage X ↔
      ∃ S : X.carrier, S ∈ X.seedSchemes ∧ X.toScheme.obj S = T := Iff.rfl

/-- The ambient target schemes and mapped presieves represented by the selected
covering families of a chosen big-site presentation. -/
def seedCoveringsImage (X : ChosenBigSite.{u, v} P) :
    Set (Σ T : Scheme.{u}, Presieve T) :=
  { q | ∃ (T : X.carrier) (R : Presieve T),
      R ∈ X.seedCoverings T ∧
        q = ⟨X.toScheme.obj T, R.map X.toScheme⟩ }

/-- Membership in the ambient image of the selected covering families of a
chosen big-site presentation. -/
theorem mem_seedCoveringsImage_iff (X : ChosenBigSite.{u, v} P)
    (q : Σ T : Scheme.{u}, Presieve T) :
    q ∈ seedCoveringsImage X ↔
      ∃ (T : X.carrier) (R : Presieve T),
        R ∈ X.seedCoverings T ∧
          q = ⟨X.toScheme.obj T, R.map X.toScheme⟩ := Iff.rfl

/-- Extension of the selected input data only. This says nothing about
containment of the entire site. -/
def IsSeedExtension (X : ChosenBigSite.{u, v} P) (Y : ChosenBigSite.{u, w} P) : Prop :=
  seedSchemesImage X ⊆ seedSchemesImage Y ∧
    seedCoveringsImage X ⊆ seedCoveringsImage Y

/-- An actual inclusion of presentations: a functor commuting with the scheme
functors and carrying every covering family to a covering family. The equality
is strict, so every underlying scheme of the source occurs in the target.
No condition on the seed sets can supply this data. -/
structure Inclusion (X : ChosenBigSite.{u, v} P) (Y : ChosenBigSite.{u, w} P) where
  /-- The actual comparison on all objects and morphisms. -/
  functor : X.carrier ⥤ Y.carrier
  /-- The comparison leaves underlying schemes and scheme morphisms unchanged. -/
  over : functor ⋙ Y.toScheme = X.toScheme
  /-- Compatibility with all covering families, not just selected seeds. -/
  map_covering : ∀ {T : X.carrier} (R : Presieve T),
    R ∈ X.pretopology T → R.map functor ∈ Y.pretopology (functor.obj T)

namespace Inclusion

/-- Identity inclusion, independent of the seed selection. -/
def refl (X : ChosenBigSite.{u, v} P) : Inclusion X X where
  functor := 𝟭 X.carrier
  over := rfl
  map_covering {T} R hR := by
    change R.map (𝟭 X.carrier) ∈ X.pretopology T
    rw [Presieve.map_id]
    exact hR

/-- The inverse on hom sets is obtained from the given fully faithful scheme
functor. No inverse or object is selected from an existence theorem. -/
def fullyFaithful {X : ChosenBigSite.{u, v} P} {Y : ChosenBigSite.{u, w} P}
    (I : Inclusion X Y) : I.functor.FullyFaithful := by
  letI := Y.fullyFaithful.faithful
  exact Functor.FullyFaithful.ofCompFaithful (I.over.symm ▸ X.fullyFaithful)

/-- Every object of the source is an actual underlying scheme of the target. -/
theorem schemesImage_subset {X : ChosenBigSite.{u, v} P} {Y : ChosenBigSite.{u, w} P}
    (I : Inclusion X Y) : Set.range X.toScheme.obj ⊆ Set.range Y.toScheme.obj := by
  rintro T ⟨S, rfl⟩
  exact ⟨I.functor.obj S, congrArg (fun F ↦ F.obj S) I.over⟩

end Inclusion

/-- Actual site containment means existence of a comparison over schemes
preserving all covering families. It does not require a particular seed choice. -/
def IsContainedIn (X : ChosenBigSite.{u, v} P) (Y : ChosenBigSite.{u, w} P) : Prop :=
  Nonempty (Inclusion X Y)

/-- The witness includes the actual functor and its covering compatibility. -/
theorem isContainedIn_iff (X : ChosenBigSite.{u, v} P) (Y : ChosenBigSite.{u, w} P) :
    IsContainedIn X Y ↔ Nonempty (Inclusion X Y) := Iff.rfl

/-- A family of presentations of a pretopology has a common site containing
all its objects and coverings. The output universe accommodates the ambient
scheme category and the input universes; no smallness or universe lowering is
asserted. The pretopology assumption supplies closure of covering families. -/
theorem exists_common (J : Pretopology Scheme.{u}) {ι : Type w}
    (X : ι → ChosenBigSite.{u, v} J.toPrecoverage) :
    ∃ Y : ChosenBigSite.{u, max (u + 1) v w} J.toPrecoverage,
      ∀ i, IsContainedIn (X i) Y := sorry

end AlgebraicGeometry.ChosenBigSite

namespace AlgebraicGeometry.SchAlphaBigSite

/-- Stacks, Tag 022J, for the anchored big-site model of Tag 000J. A set of
big Zariski, fppf, or étale sites has a common anchored big site containing all
objects and covering families. The input ordinals form a `u`-small family;
the carrier universe is not lowered. This is an existence statement only:
no site or comparison data is chosen from its proof. -/
theorem exists_common (P : Precoverage Scheme.{u})
    (hP : P = Scheme.zariskiPrecoverage ∨ P = Scheme.fppfPrecoverage ∨
      P = Scheme.etalePrecoverage) {ι : Type u}
    (X : ι → SchAlphaBigSite.{u, v} P) :
    ∃ Y : SchAlphaBigSite.{u, max (u + 1) v} P,
      ∀ i, ChosenBigSite.IsContainedIn (X i).toChosenBigSite Y.toChosenBigSite := sorry

end AlgebraicGeometry.SchAlphaBigSite
