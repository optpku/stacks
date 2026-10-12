/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Schematic locus of an algebraic space

The largest open subspace of an algebraic space which is a scheme, constructed
as the open subspace cut out by the union of images of open immersions from
schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The underlying points of the schematic locus of `X`, namely the union of
images of open immersions `ofOver U ⟶ X`. -/
def schematicLocusPoints {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | ∃ (U : Over S) (ι : ofOver U ⟶ X),
    IsOpenImmersion ι ∧ x ∈ Set.range (Points.map ι)}

/-- A point of `X` lies in `schematicLocusPoints X` if and only if it is in the
image of some open immersion from a scheme over `S`. -/
theorem mem_schematicLocusPoints_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {x : Points X} :
    x ∈ schematicLocusPoints X ↔
      ∃ (U : Over S) (ι : ofOver U ⟶ X),
        IsOpenImmersion ι ∧ x ∈ Set.range (Points.map ι) :=
  sorry

/-- The image of an open immersion from a scheme over `S` lands in
`schematicLocusPoints X`. -/
theorem schematicLocusPoints_of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} {ι : ofOver U ⟶ X} [IsOpenImmersion ι] :
    Set.range (Points.map ι) ⊆ schematicLocusPoints X :=
  sorry

/-- The morphism of algebraic spaces associated to a Yoneda section of `X`. -/
def ofYonedaSection {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : ofOver U.unop ⟶ X :=
  yonedaEquiv.symm α

/-- The subfunctor of maps into `X` whose image of points lands in the schematic
locus of `X`. -/
def schematicLocusSubfunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Subfunctor X.functorOfPoints where
  obj U := {φ | Set.range (Points.map (ofYonedaSection φ)) ⊆ schematicLocusPoints X}
  map := sorry

/-- The algebraic space underlying the schematic locus of `X`. -/
def schematicLocusSpace {S : Scheme.{u}} (X : AlgebraicSpace S) : AlgebraicSpace S :=
  ofFunctor (schematicLocusSubfunctor X).toFunctor sorry sorry sorry

/-- The inclusion of the schematic locus of `X` into `X`. -/
def schematicLocusι {S : Scheme.{u}} (X : AlgebraicSpace S) :
    schematicLocusSpace X ⟶ X :=
  (schematicLocusSubfunctor X).ι

/-- The inclusion of the schematic locus is an open immersion. -/
instance instIsOpenImmersion_schematicLocusι {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsOpenImmersion (schematicLocusι X) :=
  sorry

/-- The largest open subspace of `X` which is a scheme. -/
def schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S) : OpenSubspace X :=
  OpenSubspace.ofι (schematicLocusι X)

/-- The inclusion of `schematicLocus X` is an open immersion. -/
instance instIsOpenImmersion_schematicLocus_ι {S : Scheme.{u}}
    (X : AlgebraicSpace S) : IsOpenImmersion (schematicLocus X).ι :=
  (schematicLocus X).isOpenImmersion

/-- The schematic locus of `X` is a scheme. -/
instance instIsScheme_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsScheme (schematicLocus X).X :=
  sorry

/-- Every open subspace of `X` which is a scheme factors through the schematic
locus. -/
theorem le_schematicLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] :
    ∃ f : V.X ⟶ (schematicLocus X).X, f ≫ (schematicLocus X).ι = V.ι :=
  sorry

/-- The factorization of an open subspace which is a scheme through the schematic
locus is unique. -/
theorem existsUnique_le_schematicLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : OpenSubspace X) [IsScheme V.X] :
    ∃! f : V.X ⟶ (schematicLocus X).X, f ≫ (schematicLocus X).ι = V.ι :=
  sorry

/-- A point of `X` lies in the schematic locus if and only if it lies in the
union of images of open immersions from schemes. -/
theorem mem_schematicLocus_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    x ∈ Set.range (Points.map (schematicLocus X).ι) ↔
      x ∈ schematicLocusPoints X :=
  sorry

/-- The schematic locus is the open subspace cut out by the pointwise schematic
subfunctor, included by an open immersion, whose underlying space is a scheme,
and whose points are the union of images of open immersions from schemes. -/
theorem schematicLocus_spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (schematicLocusSpace X).functorOfPoints =
        (schematicLocusSubfunctor X).toFunctor ∧
      schematicLocusι X = (schematicLocusSubfunctor X).ι ∧
      IsOpenImmersion (schematicLocusι X) ∧
      IsScheme (schematicLocus X).X ∧
      ∀ x : Points X,
        x ∈ Set.range (Points.map (schematicLocus X).ι) ↔
          x ∈ schematicLocusPoints X :=
  sorry

/-- If `X` itself is a scheme, then the schematic locus inclusion is an
isomorphism. -/
instance instIsIso_schematicLocus_ι {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsScheme X] : IsIso (schematicLocus X).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
