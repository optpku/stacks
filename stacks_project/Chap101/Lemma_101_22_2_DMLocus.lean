/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Membership in the DM and quasi-DM loci

A point of an algebraic stack lies in the DM locus when it lies on some open
DM substack, and in the quasi-DM locus when it lies on some open quasi-DM
substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A point of an algebraic stack lies in the DM locus if it lies on some open
DM substack. -/
def memDMLocus {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X) : Prop :=
  ∃ U : OpenSubstack X, IsDM U.Y ∧ x ∈ Set.range (Points.map U.ι)

/-- A point lies in the DM locus if and only if it lies on some open DM
substack. -/
theorem memDMLocus_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (x : Points X) :
    memDMLocus x ↔
      ∃ U : OpenSubstack X, IsDM U.Y ∧ x ∈ Set.range (Points.map U.ι) :=
  sorry

/-- Membership in the image of an open DM substack witnesses DM-locus
membership. -/
theorem memDMLocus.of {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (U : OpenSubstack X) (hU : IsDM U.Y)
    (hx : x ∈ Set.range (Points.map U.ι)) :
    memDMLocus x :=
  sorry

/-- DM-locus membership yields an open DM substack through which the point
factors. -/
theorem memDMLocus.spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : memDMLocus x) :
    ∃ U : OpenSubstack X, IsDM U.Y ∧ x ∈ Set.range (Points.map U.ι) :=
  sorry

/-- A point of an algebraic stack lies in the quasi-DM locus if it lies on some
open quasi-DM substack. -/
def memQuasiDMLocus {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X) : Prop :=
  ∃ U : OpenSubstack X, IsQuasiDM U.Y ∧ x ∈ Set.range (Points.map U.ι)

/-- A point lies in the quasi-DM locus if and only if it lies on some open
quasi-DM substack. -/
theorem memQuasiDMLocus_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (x : Points X) :
    memQuasiDMLocus x ↔
      ∃ U : OpenSubstack X, IsQuasiDM U.Y ∧ x ∈ Set.range (Points.map U.ι) :=
  sorry

/-- Membership in the image of an open quasi-DM substack witnesses quasi-DM-locus
membership. -/
theorem memQuasiDMLocus.of {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (U : OpenSubstack X)
    (hU : IsQuasiDM U.Y) (hx : x ∈ Set.range (Points.map U.ι)) :
    memQuasiDMLocus x :=
  sorry

/-- Quasi-DM-locus membership yields an open quasi-DM substack through which the
point factors. -/
theorem memQuasiDMLocus.spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : memQuasiDMLocus x) :
    ∃ U : OpenSubstack X, IsQuasiDM U.Y ∧ x ∈ Set.range (Points.map U.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
