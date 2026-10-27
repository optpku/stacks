/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace

/-- Points lying in an open scheme subspace of the algebraic space. -/
def schematicLocusPoints {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | ∃ (U : Over S) (ι : ofOver U ⟶ X),
    IsOpenImmersion ι ∧ x ∈ Set.range (Points.map ι)}

/-- Membership in the schematic locus means lying in the image of an open scheme subspace. -/
theorem mem_schematicLocusPoints_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    x ∈ schematicLocusPoints X ↔ ∃ (U : Over S) (ι : ofOver U ⟶ X),
      IsOpenImmersion ι ∧ x ∈ Set.range (Points.map ι) := Iff.rfl

/-- The image of every open scheme subspace lies in the schematic locus. -/
theorem schematicLocusPoints_of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} {ι : ofOver U ⟶ X} [IsOpenImmersion ι] :
    Set.range (Points.map ι) ⊆ schematicLocusPoints X :=
  fun _ hx ↦ ⟨U, ι, inferInstance, hx⟩

/-- The union of open scheme images is open. -/
theorem isOpen_schematicLocusPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsOpen (schematicLocusPoints X) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨U, ι, hι, hx⟩
  letI : IsOpenImmersion ι := hι
  exact Filter.mem_of_superset
    ((OpenSubspace.isOpen_pointsSet (OpenSubspace.ofι ι)).mem_nhds hx)
    (schematicLocusPoints_of (ι := ι))

/-- The schematic locus as an open set of points. -/
def schematicLocusOpens {S : Scheme.{u}} (X : AlgebraicSpace S) : Opens (Points X) :=
  ⟨schematicLocusPoints X, isOpen_schematicLocusPoints X⟩

/-- The largest open subspace of an algebraic space that is representable by a scheme. -/
def schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S) : OpenSubspace X :=
  OpenSubspace.fromOpens (schematicLocusOpens X)

/-- A section of the functor of points determines a morphism from its representing scheme. -/
def ofYonedaSection {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : ofOver U.unop ⟶ X := yonedaEquiv.symm α

/-- The subfunctor consisting of sections with image in the schematic locus. -/
abbrev schematicLocusSubfunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  OpenSubspace.Construction.subfunctor X (schematicLocusOpens X)

/-- The algebraic space underlying the schematic locus. -/
abbrev schematicLocusSpace {S : Scheme.{u}} (X : AlgebraicSpace S) : AlgebraicSpace S :=
  (schematicLocus X).X

/-- The inclusion of the schematic locus into the algebraic space. -/
abbrev schematicLocusι {S : Scheme.{u}} (X : AlgebraicSpace S) := (schematicLocus X).ι

/-- The structure morphism of the schematic locus is an open immersion. -/
instance instIsOpenImmersion_schematicLocus_ι {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsOpenImmersion (schematicLocus X).ι := (schematicLocus X).isOpenImmersion

/-- The schematic locus of an algebraic space is representable by a scheme. -/
instance instIsScheme_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsScheme (schematicLocus X).X := sorry

/-- An open representable subspace has image contained in the schematic locus. -/
theorem schematicLocusPoints_range {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] :
    Set.range (Points.map V.ι) ⊆ schematicLocusPoints X := by
  obtain ⟨U, ⟨e⟩⟩ := IsScheme.spec V.X
  let e' : V.X.functorOfPoints ≅ (ofOver U).functorOfPoints :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
  have hι : IsOpenImmersion (e.inv ≫ V.ι) := by
    exact ⟨MorphismProperty.RespectsIso.precomp
      (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion)).presheaf
      e'.inv V.ι V.isOpenImmersion.presheaf⟩
  rintro x ⟨y, rfl⟩
  refine ⟨U, e.inv ≫ V.ι, hι, Points.map e.hom y, ?_⟩
  rw [Points.map_comp, ← Points.map_comp e.hom e.inv, e.hom_inv_id, Points.map_id]

/-- Factor through the actual open subtype by retaining every scheme-valued section. -/
def schematicLocusLift {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] : V.X ⟶ (schematicLocus X).X :=
  OpenSubspace.Construction.lift V.ι (schematicLocusPoints_range V)

/-- The canonical lift of an open scheme subspace commutes with its inclusion. -/
@[reassoc] theorem schematicLocusLift_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] :
    schematicLocusLift V ≫ (schematicLocus X).ι = V.ι := rfl

/-- Every open scheme subspace factors through the schematic locus. -/
theorem le_schematicLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] :
    ∃ f : V.X ⟶ (schematicLocus X).X, f ≫ (schematicLocus X).ι = V.ι :=
  ⟨schematicLocusLift V, schematicLocusLift_ι V⟩

/-- Every algebraic space over a scheme has a largest open subspace representable by a scheme. -/
theorem exists_largest_open_scheme {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧
      ∀ (V : OpenSubspace X), IsScheme V.X →
        ∃ f : V.X ⟶ U.X, f ≫ U.ι = V.ι := by
  refine ⟨schematicLocus X, instIsScheme_schematicLocus X, ?_⟩
  intro V hV
  exact @le_schematicLocus S X V hV

/-- An open scheme subspace factors uniquely through the schematic locus. -/
theorem existsUnique_le_schematicLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] :
    ∃! f : V.X ⟶ (schematicLocus X).X, f ≫ (schematicLocus X).ι = V.ι := by
  refine ⟨schematicLocusLift V, schematicLocusLift_ι V, ?_⟩
  intro f hf
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact congrArg (fun k : V.X ⟶ X ↦ k.app T s) hf

/-- A point lies in the image of the schematic locus exactly when it lies in an open scheme subspace. -/
theorem mem_schematicLocus_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    x ∈ Set.range (Points.map (schematicLocus X).ι) ↔ x ∈ schematicLocusPoints X := by
  change x ∈ (OpenSubspace.fromOpens (schematicLocusOpens X)).pointsSet ↔ _
  rw [OpenSubspace.fromOpens_pointsSet]
  rfl

/-- The schematic locus is the open representable subfunctor of sections with schematic image. -/
theorem schematicLocus_spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (schematicLocusSpace X).functorOfPoints = (schematicLocusSubfunctor X).toFunctor ∧
      schematicLocusι X = (schematicLocusSubfunctor X).ι ∧
      IsOpenImmersion (schematicLocusι X) ∧ IsScheme (schematicLocus X).X ∧
      ∀ x : Points X, x ∈ Set.range (Points.map (schematicLocus X).ι) ↔
        x ∈ schematicLocusPoints X :=
  ⟨rfl, rfl, inferInstance, inferInstance, fun x ↦ mem_schematicLocus_iff x⟩

/-- Every point of a representable algebraic space lies in its schematic locus. -/
theorem schematicLocusPoints_eq_univ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    schematicLocusPoints X = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  haveI : IsScheme (OpenSubspace.id X).X := by
    change IsScheme X
    infer_instance
  exact schematicLocusPoints_range (OpenSubspace.id X) ⟨x, Points.map_id x⟩

/-- A representable algebraic space maps to its schematic locus by the identity on sections. -/
def schematicLocusInverse {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    X ⟶ (schematicLocus X).X :=
  OpenSubspace.Construction.lift (𝟙 X) (by
    change Set.range (Points.map (𝟙 X)) ⊆ schematicLocusPoints X
    rw [schematicLocusPoints_eq_univ X]
    exact Set.subset_univ _)

/-- The inclusion of the schematic locus followed by its inverse is the identity. -/
theorem schematicLocus_hom_inv_id {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    (schematicLocus X).ι ≫ schematicLocusInverse X = 𝟙 (schematicLocus X).X := by
  change (schematicLocusSubfunctor X).ι ≫
    (schematicLocusInverse X : X.functorOfPoints ⟶ (schematicLocusSubfunctor X).toFunctor) =
      𝟙 (schematicLocusSubfunctor X).toFunctor
  rfl

/-- The inverse to the schematic-locus inclusion followed by the inclusion is the identity. -/
theorem schematicLocus_inv_hom_id {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    schematicLocusInverse X ≫ (schematicLocus X).ι = 𝟙 X := rfl

/-- A representable algebraic space is isomorphic to its schematic locus. -/
def schematicLocusIso {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    (schematicLocus X).X ≅ X where
  hom := (schematicLocus X).ι
  inv := schematicLocusInverse X
  hom_inv_id := schematicLocus_hom_inv_id X
  inv_hom_id := schematicLocus_inv_hom_id X

/-- The schematic-locus inclusion of a representable algebraic space is an isomorphism. -/
instance instIsIso_schematicLocus_ι {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    IsIso (schematicLocus X).ι := (schematicLocusIso X).isIso_hom

end AlgebraicGeometry.AlgebraicSpace
