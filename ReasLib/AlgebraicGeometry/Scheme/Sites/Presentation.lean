/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation

/-!
# Containment of chosen big-site presentations

Selected schemes and covering families in a chosen presentation have images in
the ambient category of schemes. These images give the natural containment
relation between presentations and have common extensions for small indexed
families.
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
      ∃ S : X.carrier, S ∈ X.seedSchemes ∧ X.toScheme.obj S = T := sorry

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
          q = ⟨X.toScheme.obj T, R.map X.toScheme⟩ := sorry

/-- A chosen big-site presentation is contained in a possibly differently
universe-sized presentation when the images of its selected objects and covering
families are included in the corresponding images of the other presentation. -/
def IsContainedIn (X : ChosenBigSite.{u, v} P) (Y : ChosenBigSite.{u, w} P) : Prop :=
  seedSchemesImage X ⊆ seedSchemesImage Y ∧
    seedCoveringsImage X ⊆ seedCoveringsImage Y

/-- Cross-universe containment of chosen big-site presentations is exactly
simultaneous inclusion of their selected scheme and covering-family images. -/
theorem isContainedIn_iff (X : ChosenBigSite.{u, v} P) (Y : ChosenBigSite.{u, w} P) :
    IsContainedIn X Y ↔
      seedSchemesImage X ⊆ seedSchemesImage Y ∧
        seedCoveringsImage X ⊆ seedCoveringsImage Y := sorry

/-- Every universe-small indexed family of chosen presentations for a fixed
scheme precoverage is contained in a common presentation whose morphisms live
in the canonical universe of morphisms between the ambient schemes. -/
theorem exists_common (P : Precoverage Scheme.{u}) {ι : Type u}
    (X : ι → ChosenBigSite.{u, v} P) :
    ∃ Y : ChosenBigSite.{u, u} P, ∀ i, IsContainedIn (X i) Y := sorry

end AlgebraicGeometry.ChosenBigSite
