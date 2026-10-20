/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Lemma_100_9_12_Opens
public import stacks_project.Chap100.Lemma_100_9_14_Union
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Open DM and quasi-DM loci of an algebraic stack

The largest open DM substack and the largest open quasi-DM substack of an
algebraic stack, constructed as the unions of all open substacks with those
properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The family of open DM substacks of an algebraic stack. -/
def dmOpenFamily {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    {U : OpenSubstack X // IsDM U.Y} → OpenSubstack X :=
  Subtype.val

/-- The largest open DM substack of an algebraic stack. -/
def dmLocus {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    OpenSubstack X :=
  OpenSubstack.iUnion dmOpenFamily

/-- The largest open DM substack of an algebraic stack is DM. -/
instance instIsDM_dmLocus {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] : IsDM (dmLocus X).Y :=
  sorry

/-- Any open DM substack is contained in the largest open DM substack on
points. -/
theorem dmLocus_maximal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (V : OpenSubstack X) (hV : IsDM V.Y) :
    V.pointsSet ⊆ (dmLocus X).pointsSet :=
  sorry

/-- A point of an algebraic stack lies on the largest open DM substack if and
only if it lies on some open DM substack. -/
theorem dmLocus_pointsSet_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    x ∈ (dmLocus X).pointsSet ↔
      ∃ U : OpenSubstack X, IsDM U.Y ∧ x ∈ U.pointsSet :=
  sorry

/-- The largest open DM substack is the `iUnion` of the open DM substacks, is
itself DM, and contains every competing open DM substack on points. -/
theorem dmLocus_spec {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (dmLocus X).objectProperty =
        OpenSubstack.objectProperty_iUnion dmOpenFamily ∧
      IsDM (dmLocus X).Y ∧
      ∀ V : OpenSubstack X, IsDM V.Y →
        V.pointsSet ⊆ (dmLocus X).pointsSet :=
  sorry

/-- The family of open quasi-DM substacks of an algebraic stack. -/
def quasiDMOpenFamily {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] :
    {U : OpenSubstack X // IsQuasiDM U.Y} → OpenSubstack X :=
  Subtype.val

/-- The largest open quasi-DM substack of an algebraic stack. -/
def quasiDMLocus {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    OpenSubstack X :=
  OpenSubstack.iUnion quasiDMOpenFamily

/-- The largest open quasi-DM substack of an algebraic stack is quasi-DM. -/
instance instIsQuasiDM_quasiDMLocus {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] : IsQuasiDM (quasiDMLocus X).Y :=
  sorry

/-- Any open quasi-DM substack is contained in the largest open quasi-DM
substack on points. -/
theorem quasiDMLocus_maximal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (V : OpenSubstack X) (hV : IsQuasiDM V.Y) :
    V.pointsSet ⊆ (quasiDMLocus X).pointsSet :=
  sorry

/-- A point of an algebraic stack lies on the largest open quasi-DM substack if
and only if it lies on some open quasi-DM substack. -/
theorem quasiDMLocus_pointsSet_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    x ∈ (quasiDMLocus X).pointsSet ↔
      ∃ U : OpenSubstack X, IsQuasiDM U.Y ∧ x ∈ U.pointsSet :=
  sorry

/-- The largest open quasi-DM substack is the `iUnion` of the open quasi-DM
substacks, is itself quasi-DM, and contains every competing open quasi-DM
substack on points. -/
theorem quasiDMLocus_spec {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (quasiDMLocus X).objectProperty =
        OpenSubstack.objectProperty_iUnion quasiDMOpenFamily ∧
      IsQuasiDM (quasiDMLocus X).Y ∧
      ∀ V : OpenSubstack X, IsQuasiDM V.Y →
        V.pointsSet ⊆ (quasiDMLocus X).pointsSet :=
  sorry

/-- The largest open DM substack is contained in the largest open quasi-DM
substack on points. -/
theorem dmLocus_le_quasiDMLocus {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (dmLocus X).pointsSet ⊆ (quasiDMLocus X).pointsSet :=
  sorry

/-- The inclusion of the largest open DM substack factors through the largest
open quasi-DM substack. -/
theorem dmLocus_factorsThrough_quasiDMLocus {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    FactorsThrough (dmLocus X).ι (quasiDMLocus X).ι :=
  sorry

end AlgebraicGeometry.AlgebraicStack
