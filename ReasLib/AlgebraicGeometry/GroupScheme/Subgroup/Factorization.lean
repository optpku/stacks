module

public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup
public import ReasLib.CategoryTheory.Monoidal.Grp.Factorization

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace CategoryTheory.GrpObj.Restriction

variable {S : AlgebraicGeometry.Scheme.{u}} {H G : Over S} [GrpObj G] {j : H ⟶ G}

/-- Regard a compatible restriction along a closed immersion as a closed subgroup scheme. -/
noncomputable abbrev toClosedSubgroup (R : GrpObj.Restriction j)
    [AlgebraicGeometry.IsClosedImmersion j.left] :
    AlgebraicGeometry.Scheme.ClosedSubgroup G :=
  MorphismProperty.Over.mk ⊤ R.hom <| by
    dsimp [MorphismProperty.inverseImage]
    have h :
        Over.Hom.left ((Grp.forget (Over S)).map R.hom) = Over.Hom.left j := by
      simpa [R.hom_hom]
    exact h ▸ (inferInstance : AlgebraicGeometry.IsClosedImmersion (Over.Hom.left j))

/-- Regard a compatible restriction along an open immersion as an open subgroup scheme. -/
noncomputable abbrev toOpenSubgroup (R : GrpObj.Restriction j)
    [AlgebraicGeometry.IsOpenImmersion j.left] :
    AlgebraicGeometry.Scheme.OpenSubgroup G :=
  MorphismProperty.Over.mk ⊤ R.hom <| by
    dsimp [MorphismProperty.inverseImage]
    have h :
        Over.Hom.left ((Grp.forget (Over S)).map R.hom) = Over.Hom.left j := by
      simpa [R.hom_hom]
    exact h ▸ (inferInstance : AlgebraicGeometry.IsOpenImmersion (Over.Hom.left j))

end CategoryTheory.GrpObj.Restriction

namespace AlgebraicGeometry.Scheme.ClosedSubgroup

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

/-- View the group-object structure and inclusion of a closed subgroup scheme as a compatible
restriction. -/
def toRestriction (K : ClosedSubgroup G) :
    GrpObj.Restriction K.inclusion where
  grpObj := K.left.grp
  hom := K.hom
  hom_hom := rfl

/-- View a closed subgroup scheme as explicit factorizations of the unit, multiplication, and
inverse through its inclusion. -/
noncomputable abbrev toFactorization (K : ClosedSubgroup G) :
    GrpObj.Factorization K.inclusion :=
  K.toRestriction.toFactorization

/-- Passing from a closed subgroup scheme to its restriction view and back recovers it. -/
theorem toRestriction_toClosedSubgroup (K : ClosedSubgroup G) :
    K.toRestriction.toClosedSubgroup = K := by
  cases K
  rfl

end AlgebraicGeometry.Scheme.ClosedSubgroup

namespace AlgebraicGeometry.Scheme.OpenSubgroup

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

/-- View the group-object structure and inclusion of an open subgroup scheme as a compatible
restriction. -/
def toRestriction (K : OpenSubgroup G) :
    GrpObj.Restriction K.inclusion where
  grpObj := K.left.grp
  hom := K.hom
  hom_hom := rfl

/-- View an open subgroup scheme as explicit factorizations of the unit, multiplication, and
inverse through its inclusion. -/
noncomputable abbrev toFactorization (K : OpenSubgroup G) :
    GrpObj.Factorization K.inclusion :=
  K.toRestriction.toFactorization

/-- Passing from an open subgroup scheme to its restriction view and back recovers it. -/
theorem toRestriction_toOpenSubgroup (K : OpenSubgroup G) :
    K.toRestriction.toOpenSubgroup = K := by
  cases K
  rfl

end AlgebraicGeometry.Scheme.OpenSubgroup

namespace CategoryTheory.GrpObj.Restriction

variable {S : AlgebraicGeometry.Scheme.{u}} {H G : Over S} [GrpObj G] {j : H ⟶ G}

/-- The inclusion of the closed subgroup scheme induced by `R` is `j`. -/
theorem toClosedSubgroup_inclusion (R : GrpObj.Restriction j)
    [AlgebraicGeometry.IsClosedImmersion j.left] :
    HEq R.toClosedSubgroup.inclusion j := by
  dsimp [toClosedSubgroup, ClosedSubgroup.inclusion, MorphismProperty.Over.mk]
  exact R.hom_hom.heq

/-- Passing from a compatible restriction to a closed subgroup scheme and back recovers the
original restriction. -/
@[simp]
theorem toClosedSubgroup_toRestriction (R : GrpObj.Restriction j)
    [AlgebraicGeometry.IsClosedImmersion j.left] :
    HEq (R.toClosedSubgroup.toRestriction) R := by
  cases R with
  | mk grpObj hom hom_hom =>
      cases hom_hom
      rfl

/-- The inclusion of the open subgroup scheme induced by `R` is `j`. -/
theorem toOpenSubgroup_inclusion (R : GrpObj.Restriction j)
    [AlgebraicGeometry.IsOpenImmersion j.left] :
    HEq R.toOpenSubgroup.inclusion j := by
  dsimp [toOpenSubgroup, OpenSubgroup.inclusion, MorphismProperty.Over.mk]
  exact R.hom_hom.heq

/-- Passing from a compatible restriction to an open subgroup scheme and back recovers the
original restriction. -/
@[simp]
theorem toOpenSubgroup_toRestriction (R : GrpObj.Restriction j)
    [AlgebraicGeometry.IsOpenImmersion j.left] :
    HEq (R.toOpenSubgroup.toRestriction) R := by
  cases R with
  | mk grpObj hom hom_hom =>
      cases hom_hom
      rfl

end CategoryTheory.GrpObj.Restriction

namespace CategoryTheory.GrpObj.Factorization

variable {S : AlgebraicGeometry.Scheme.{u}} {H G : Over S} [GrpObj G] {j : H ⟶ G}

/-- Regard factor maps through a closed immersion as a closed subgroup scheme on the source. -/
noncomputable abbrev toClosedSubgroup (F : GrpObj.Factorization j)
    [AlgebraicGeometry.IsClosedImmersion j.left] :
    AlgebraicGeometry.Scheme.ClosedSubgroup G := by
  -- Local instance justification (proof-local temporary data): the closed immersion makes `j.left` monic for the generic construction.
  letI : Mono j := Over.mono_of_mono_left j
  exact F.toRestriction.toClosedSubgroup

/-- The inclusion of the closed subgroup scheme induced by `F` is `j`. -/
theorem toClosedSubgroup_inclusion (F : GrpObj.Factorization j)
    [AlgebraicGeometry.IsClosedImmersion j.left] :
    HEq F.toClosedSubgroup.inclusion j := by
  -- Local instance justification (proof-local temporary data): the closed immersion makes `j.left` monic for the generic construction.
  letI : Mono j := Over.mono_of_mono_left j
  simpa [toClosedSubgroup] using
    Restriction.toClosedSubgroup_inclusion F.toRestriction

/-- Regard factor maps through an open immersion as an open subgroup scheme on the source. -/
noncomputable abbrev toOpenSubgroup (F : GrpObj.Factorization j)
    [AlgebraicGeometry.IsOpenImmersion j.left] :
    AlgebraicGeometry.Scheme.OpenSubgroup G := by
  -- Local instance justification (proof-local temporary data): the open immersion makes `j.left` monic for the generic construction.
  letI : Mono j := Over.mono_of_mono_left j
  exact F.toRestriction.toOpenSubgroup

/-- The inclusion of the open subgroup scheme induced by `F` is `j`. -/
theorem toOpenSubgroup_inclusion (F : GrpObj.Factorization j)
    [AlgebraicGeometry.IsOpenImmersion j.left] :
    HEq F.toOpenSubgroup.inclusion j := by
  -- Local instance justification (proof-local temporary data): the open immersion makes `j.left` monic for the generic construction.
  letI : Mono j := Over.mono_of_mono_left j
  simpa [toOpenSubgroup] using
    Restriction.toOpenSubgroup_inclusion F.toRestriction

end CategoryTheory.GrpObj.Factorization

namespace AlgebraicGeometry.Scheme.ClosedSubgroup

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

open CategoryTheory.GrpObj

/-- Passing from a closed subgroup scheme to its factorization view and back recovers it. -/
theorem toFactorization_toClosedSubgroup (K : ClosedSubgroup G) :
    K.toFactorization.toClosedSubgroup = K := by
  -- Local instance justification (proof-local temporary data): the closed subgroup inclusion is monic during the generic round trip.
  letI : Mono K.inclusion := Over.mono_of_mono_left K.inclusion
  have h :
      K.toFactorization.toClosedSubgroup = K.toRestriction.toClosedSubgroup := by
    simpa [toFactorization, Factorization.toClosedSubgroup] using
      congrArg (fun R ↦ Restriction.toClosedSubgroup R)
        K.toRestriction.toFactorization_toRestriction
  exact h.trans K.toRestriction_toClosedSubgroup

end AlgebraicGeometry.Scheme.ClosedSubgroup

namespace AlgebraicGeometry.Scheme.OpenSubgroup

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

open CategoryTheory.GrpObj

/-- Passing from an open subgroup scheme to its factorization view and back recovers it. -/
theorem toFactorization_toOpenSubgroup (K : OpenSubgroup G) :
    K.toFactorization.toOpenSubgroup = K := by
  -- Local instance justification (proof-local temporary data): the open subgroup inclusion is monic during the generic round trip.
  letI : Mono K.inclusion := Over.mono_of_mono_left K.inclusion
  have h :
      K.toFactorization.toOpenSubgroup = K.toRestriction.toOpenSubgroup := by
    simpa [toFactorization, Factorization.toOpenSubgroup] using
      congrArg (fun R ↦ Restriction.toOpenSubgroup R)
        K.toRestriction.toFactorization_toRestriction
  exact h.trans K.toRestriction_toOpenSubgroup

end AlgebraicGeometry.Scheme.OpenSubgroup

namespace AlgebraicGeometry

/-- A closed immersion into a group scheme admits a compatible group-object restriction exactly
when the unit, restricted multiplication, and inverse factor through its source. -/
theorem closedSubgroup_iff_factorization {S : Scheme.{u}} {H G : Over S}
    [GrpObj G] (j : H ⟶ G) [IsClosedImmersion j.left] :
    Nonempty (GrpObj.Restriction j) ↔ Nonempty (GrpObj.Factorization j) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toFactorization⟩
  · rintro ⟨F⟩
    -- Local instance justification (proof-local temporary data): the closed immersion makes `j.left` monic for the generic construction.
    letI : Mono j := Over.mono_of_mono_left j
    exact ⟨F.toRestriction⟩

/-- An open immersion into a group scheme admits a compatible group-object restriction exactly
when the unit, restricted multiplication, and inverse factor through its source. -/
theorem openSubgroup_iff_factorization {S : Scheme.{u}} {H G : Over S}
    [GrpObj G] (j : H ⟶ G) [IsOpenImmersion j.left] :
    Nonempty (GrpObj.Restriction j) ↔ Nonempty (GrpObj.Factorization j) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toFactorization⟩
  · rintro ⟨F⟩
    -- Local instance justification (proof-local temporary data): the open immersion makes `j.left` monic for the generic construction.
    letI : Mono j := Over.mono_of_mono_left j
    exact ⟨F.toRestriction⟩

end AlgebraicGeometry
