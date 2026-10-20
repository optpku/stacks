/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Topology

/-!
# Geometric irreducibility of group schemes

Irreducibility of a group scheme over a field persists after every field extension.
-/

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

/-- An irreducible group scheme over a field is geometrically irreducible. -/
instance instGeometricallyIrreducibleOfIrreducible
    (G : SchemeOverField k) [GrpObj G] [IrreducibleSpace G.left] :
    GeometricallyIrreducible G.hom := by
  rw [GeometricallyIrreducible.iff_forall_fieldExtension]
  intro K _ _
  let I : irreducibleComponents G.left := identityIrreducibleComponent G
  let IOver : SchemeOverField k := Over.mk (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
  let j : IOver ⟶ G := Over.homMk (G.left.irreducibleComponentSubschemeι I)
  have hIuniv : (I : Set G.left) = Set.univ := by
    have hmem : (I : Set G.left) ∈ irreducibleComponents G.left := I.2
    simpa [irreducibleComponents_eq_singleton (X := G.left)] using hmem
  have hIgeom : GeometricallyIrreducible IOver.hom := by
    change GeometricallyIrreducible (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
    exact
      geometricallyIrreducible_identityComponent G I (identity_mem_identityIrreducibleComponent G)
  have hIbase : IrreducibleSpace (FieldExtension.Over.baseChange k K IOver).left := by
    change IrreducibleSpace (FieldExtension.baseChange k K IOver.hom)
    exact (GeometricallyIrreducible.iff_forall_fieldExtension (f := IOver.hom)).mp hIgeom K
  -- Local instance justification (proof-local temporary data): use this base change only for its image below.
  letI : IrreducibleSpace (FieldExtension.Over.baseChange k K IOver).left := hIbase
  let jK : FieldExtension.Over.baseChange k K IOver ⟶ FieldExtension.Over.baseChange k K G :=
    (FieldExtension.Over.functor k K).map j
  have hRangej : Set.range j.left = Set.univ := by
    calc
      Set.range j.left = (G.left.irreducibleComponentClosed I : Set G.left) := by
        change Set.range (G.left.irreducibleComponentSubschemeι I) =
          (G.left.irreducibleComponentClosed I : Set G.left)
        exact Scheme.IdealSheafData.range_vanishingIdeal_subschemeι
          (G.left.irreducibleComponentClosed I)
      _ = (I : Set G.left) := by
        ext x
        simp
      _ = Set.univ := hIuniv
  have hRangejK : Set.range jK.left = Set.univ := by
    rw [← FieldExtension.Over.preimage_range_map (k := k) (K := K) j]
    simpa [hRangej]
  have hRangeIrreducible : IsIrreducible (Set.range jK.left) := by
    simpa [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (FieldExtension.Over.baseChange k K IOver).left).image
        jK.left.base jK.left.continuous.continuousOn
  exact (irreducibleSpace_def (FieldExtension.Over.baseChange k K G).left).2 <| by
    simpa [hRangejK] using hRangeIrreducible

end AlgebraicGeometry.GroupScheme
