/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.GroupScheme.Topology
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Jacobson
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.RationalPoint
public import ReasLib.FieldTheory.IsAlgClosed.Cardinality
public import ReasLib.Topology.Jacobson.Surjective

/-!
# Quasi-compactness of irreducible group schemes

An irreducible group scheme over a field has compact underlying topological space.
-/

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

/-- Every group scheme over a field has a nonempty affine open subset. -/
theorem exists_nonempty_affineOpen
    (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G] :
    ∃ U : G.left.affineOpens, (U : Set G.left).Nonempty := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (η[G].left (IsLocalRing.closedPoint k))) isOpen_univ
  exact ⟨⟨U, hU⟩, ⟨_, hηU⟩⟩

/-- The underlying topological space of an irreducible group scheme over a field is compact. -/
instance instCompactSpaceOfIrreducible
    (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G]
    [IrreducibleSpace G.left] : CompactSpace G.left := by
  classical
  obtain ⟨κclosed, hκclosed⟩ :=
    AlgebraicGeometry.FieldExtension.exists_cardinal_residueField_isAlgebraic_of_closedPoint G.hom
  obtain ⟨κjac, hκjac⟩ :=
    AlgebraicGeometry.FieldExtension.exists_cardinal_jacobsonSpace G.hom
  obtain ⟨K, _, _, _, hKclosed, hKjac⟩ :=
    Field.exists_algClosed_extension_cardinal_gt k κclosed κjac
  let GK : AlgebraicGeometry.SchemeOverField K := FieldExtension.Over.baseChange k K G
  have hGK_jacobson : JacobsonSpace GK.left := hκjac hKjac
  -- Local instance justification (proof-local temporary data): obtain irreducibility of this chosen base change.
  haveI : IrreducibleSpace GK.left :=
    (GeometricallyIrreducible.iff_forall_fieldExtension (f := G.hom)).mp
      (inferInstance : GeometricallyIrreducible G.hom) K
  obtain ⟨U, hU⟩ := exists_nonempty_affineOpen GK
  let eInv : GK ≅ GK := asIso ι[GK]
  -- Local instance justification (proof-local temporary data): pull back the affine open along inversion.
  haveI : IsIso ι[GK].left := by
    refine ⟨⟨eInv.inv.left, ?_, ?_⟩⟩
    · exact congrArg Over.Hom.left eInv.hom_inv_id
    · exact congrArg Over.Hom.left eInv.inv_hom_id
  let UinvOpens : GK.left.Opens := (TopologicalSpace.Opens.map ι[GK].left.base).obj U.1
  have hUinvAffine : IsAffineOpen UinvOpens := by
    simpa [UinvOpens] using (IsAffineOpen.preimage_of_isIso U.2 ι[GK].left)
  let Uinv : GK.left.affineOpens := ⟨UinvOpens, hUinvAffine⟩
  let UOver : SchemeOverField K := Over.mk (U.1.ι ≫ GK.hom)
  let UinvOver : SchemeOverField K := Over.mk (Uinv.1.ι ≫ GK.hom)
  let uOver : UOver ⟶ GK := Over.homMk U.1.ι
  let uinvOver : UinvOver ⟶ GK := Over.homMk Uinv.1.ι
  let mulOpenMap := (uOver ⊗ₘ uinvOver) ≫ μ[GK]
  have hMulOpen : IsOpen (Set.range mulOpenMap.left.base) := by
    simpa [mulOpenMap, UOver, UinvOver, uOver, uinvOver, Uinv] using
      (isOpen_range_mul_open GK U.1.ι (Uinv : GK.left.Opens))
  have hclosedSection :
      ∀ x : closedPoints GK.left,
        ∃ g : 𝟙_ (SchemeOverField K) ⟶ GK,
          g.left (IsLocalRing.closedPoint K) = x.1 := by
    intro x
    obtain ⟨gLeft, hgLeft_over, hgLeft_closed⟩ :=
      Scheme.Hom.ResidueField.exists_section_through_closedPoint_of_isAlgClosed
        GK x (hκclosed hKclosed x.1 x.2)
    refine ⟨Over.homMk gLeft hgLeft_over, hgLeft_closed⟩
  let _ := hGK_jacobson
  let _ := hMulOpen
  let _ := hclosedSection
  sorry

end AlgebraicGeometry.GroupScheme
