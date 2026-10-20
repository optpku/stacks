/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Points of the DM and quasi-DM loci

Membership in the DM and quasi-DM loci is expressed by open immersions with
DM and quasi-DM sources, respectively. For a field-valued point, these
conditions are characterized by its automorphism group over the source field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A point lies in the DM locus when it lies in the image of an open immersion
from a DM algebraic stack. -/
def memDMLocus {S : Scheme.{u}} {X : GroupoidsOver S} [hX : AlgebraicStack X]
    (x : Points X) : Prop :=
  ∃ (U : GroupoidsOver S) (hU : AlgebraicStack U) (i : U ⟶ X),
    Groupoids.Hom.OpenImmersion i ∧ @IsDM S U hU ∧
      x ∈ Set.range (@Points.map S U hU X hX i)

/-- A point lies in the DM locus exactly when an open immersion from a DM
algebraic stack contains it in its image on points. -/
theorem memDMLocus_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [hX : AlgebraicStack X] (x : Points X) :
    memDMLocus x ↔
      ∃ (U : GroupoidsOver S) (hU : AlgebraicStack U) (i : U ⟶ X),
        Groupoids.Hom.OpenImmersion i ∧ @IsDM S U hU ∧
          x ∈ Set.range (@Points.map S U hU X hX i) :=
  Iff.rfl

/-- Membership in the image of an open immersion from a DM algebraic stack
implies membership in the DM locus. -/
theorem memDMLocus.of {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (U : GroupoidsOver S)
    [hU : AlgebraicStack U] (i : U ⟶ X) (hi : Groupoids.Hom.OpenImmersion i)
    (hDM : IsDM U) (hx : x ∈ Set.range (Points.map i)) :
    memDMLocus x :=
  ⟨U, hU, i, hi, hDM, hx⟩

/-- DM-locus membership yields an open immersion from a DM algebraic stack
whose image on points contains the given point. -/
theorem memDMLocus.spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [hX : AlgebraicStack X] {x : Points X} (hx : memDMLocus x) :
    ∃ (U : GroupoidsOver S) (hU : AlgebraicStack U) (i : U ⟶ X),
      Groupoids.Hom.OpenImmersion i ∧ @IsDM S U hU ∧
        x ∈ Set.range (@Points.map S U hU X hX i) :=
  hx

/-- A point lies in the quasi-DM locus when it lies in the image of an open
immersion from a quasi-DM algebraic stack. -/
def memQuasiDMLocus {S : Scheme.{u}} {X : GroupoidsOver S}
    [hX : AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (U : GroupoidsOver S) (hU : AlgebraicStack U) (i : U ⟶ X),
    Groupoids.Hom.OpenImmersion i ∧ @IsQuasiDM S U hU ∧
      x ∈ Set.range (@Points.map S U hU X hX i)

/-- A point lies in the quasi-DM locus exactly when an open immersion from a
quasi-DM algebraic stack contains it in its image on points. -/
theorem memQuasiDMLocus_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [hX : AlgebraicStack X] (x : Points X) :
    memQuasiDMLocus x ↔
      ∃ (U : GroupoidsOver S) (hU : AlgebraicStack U) (i : U ⟶ X),
        Groupoids.Hom.OpenImmersion i ∧ @IsQuasiDM S U hU ∧
          x ∈ Set.range (@Points.map S U hU X hX i) :=
  Iff.rfl

/-- Membership in the image of an open immersion from a quasi-DM algebraic
stack implies membership in the quasi-DM locus. -/
theorem memQuasiDMLocus.of {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (U : GroupoidsOver S)
    [hU : AlgebraicStack U] (i : U ⟶ X) (hi : Groupoids.Hom.OpenImmersion i)
    (hQuasiDM : IsQuasiDM U) (hx : x ∈ Set.range (Points.map i)) :
    memQuasiDMLocus x :=
  ⟨U, hU, i, hi, hQuasiDM, hx⟩

/-- Quasi-DM-locus membership yields an open immersion from a quasi-DM
algebraic stack whose image on points contains the given point. -/
theorem memQuasiDMLocus.spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [hX : AlgebraicStack X] {x : Points X} (hx : memQuasiDMLocus x) :
    ∃ (U : GroupoidsOver S) (hU : AlgebraicStack U) (i : U ⟶ X),
      Groupoids.Hom.OpenImmersion i ∧ @IsQuasiDM S U hU ∧
        x ∈ Set.range (@Points.map S U hU X hX i) :=
  hx

/-- A field-valued point belongs to the DM locus exactly when its automorphism
group is unramified over its source field. -/
theorem memDMLocus_iff_unramified {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) :
    memDMLocus (Points.mk p) ↔
      automorphismGroup.Has (@AlgebraicSpace.Unramified S) p :=
  sorry

/-- A field-valued point belongs to the quasi-DM locus exactly when its
automorphism group is locally quasi-finite over its source field. -/
theorem memQuasiDMLocus_iff_locallyQuasiFinite {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (p : FieldValuedPoint X) :
    memQuasiDMLocus (Points.mk p) ↔
      automorphismGroup.Has (@AlgebraicSpace.LocallyQuasiFinite S) p :=
  sorry

end AlgebraicGeometry.AlgebraicStack
