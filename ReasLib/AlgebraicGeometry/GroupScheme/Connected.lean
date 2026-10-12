/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Group.ResidueField
public import ReasLib.AlgebraicGeometry.GroupScheme.IrreducibleComponent.Subgroup
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Jacobson
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.RationalPoint
public import ReasLib.FieldTheory.IsAlgClosed.Cardinality

/-!
# Connected group schemes over fields

This file relates connectedness, geometric connectedness, and irreducibility for group schemes
over fields.
-/

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

/-- A connected group scheme over a field is geometrically connected via its identity point. -/
lemma geometricallyConnected_of_connected
    (G : SchemeOverField k) [GrpObj G] [ConnectedSpace G.left] :
    GeometricallyConnected G.hom := by
  let x : G.left := η[G].left (IsLocalRing.closedPoint k)
  have hx : IsIso (G.hom.residueFieldMap x) := by
    dsimp [x]
    exact
      (RingEquiv.ofBijective (G.hom.residueFieldMap (η[G].left (IsLocalRing.closedPoint k))).hom
        (AlgebraicGeometry.Scheme.GroupTangent.unit_residueFieldMap_bijective G
          (IsLocalRing.closedPoint k))).toCommRingCatIso.isIso_hom
  exact GeometricallyConnected.ResidueField.of_connectedSpace_of_isIsoMap
    G.hom inferInstance x

/-- Every field-extension base change of a connected group scheme stays connected. -/
lemma connectedSpace_baseChange_of_connected
    (G : SchemeOverField k) [GrpObj G] [ConnectedSpace G.left]
    (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (FieldExtension.Over.baseChange k K G).left := by
  change ConnectedSpace (FieldExtension.baseChange k K G.hom)
  simpa using
    (GeometricallyConnected.iff_connectedSpace_baseChange (f := G.hom)).mp
      (geometricallyConnected_of_connected G) K

/-- Irreducibility descends from a field-extension base change along the canonical surjection on
irreducible components. -/
lemma irreducibleSpace_of_irreducible_baseChange
    {K : Type u} [Field K] [Algebra k K]
    (G : SchemeOverField k) [GrpObj G]
    [IrreducibleSpace (FieldExtension.baseChange k K G.hom)] :
    IrreducibleSpace G.left := by
  classical
  let componentMap := FieldExtension.Irreducible.componentsMap k K G.hom
  have hGKSub :
      Subsingleton (irreducibleComponents (FieldExtension.baseChange k K G.hom)) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hsurj : Function.Surjective componentMap :=
    FieldExtension.Irreducible.componentsMap_surjective k K G.hom
  have hsub : Subsingleton (irreducibleComponents G.left) :=
    @Function.Surjective.subsingleton
      (irreducibleComponents (FieldExtension.baseChange k K G.hom))
      (irreducibleComponents G.left) componentMap hGKSub hsurj
  let x : G.left := η[G].left (IsLocalRing.closedPoint k)
  have hxUniv : irreducibleComponent x = (Set.univ : Set G.left) := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      have hEq :
          (⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩ :
            irreducibleComponents G.left) =
            ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :=
        Subsingleton.elim _ _
      have hyMem :
          y ∈ ((⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩ :
            irreducibleComponents G.left) : Set G.left) :=
        mem_irreducibleComponent (x := y)
      have hyMem' :
          y ∈ ((⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :
            irreducibleComponents G.left) : Set G.left) :=
        hEq ▸ hyMem
      simpa using hyMem'
  exact (irreducibleSpace_def G.left).2 <| by
    simpa [hxUniv] using isIrreducible_irreducibleComponent (x := x)

/-- An algebraically closed connected Jacobson group scheme whose closed points are rational is
irreducible. -/
theorem irreducibleSpace_of_connected_of_algClosed_of_closedPointsRational
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : SchemeOverField K) [GrpObj G]
    [ConnectedSpace G.left] [JacobsonSpace G.left]
    (hclosed : ∀ x : closedPoints G.left,
      ∃ g : 𝟙_ (SchemeOverField K) ⟶ G, g.left (IsLocalRing.closedPoint K) = x.1) :
    IrreducibleSpace G.left := sorry

/-- The underlying space of a connected group scheme over a field is irreducible. -/
instance instIrreducibleSpaceOfConnected
    (G : SchemeOverField k) [GrpObj G]
    [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  classical
  obtain ⟨κclosed, hκclosed⟩ :=
    AlgebraicGeometry.FieldExtension.exists_cardinal_residueField_isAlgebraic_of_closedPoint G.hom
  obtain ⟨κjac, hκjac⟩ :=
    AlgebraicGeometry.FieldExtension.exists_cardinal_jacobsonSpace G.hom
  obtain ⟨K, _, _, _, hKclosed, hKjac⟩ :=
    Field.exists_algClosed_extension_cardinal_gt k κclosed κjac
  let GK : SchemeOverField K := FieldExtension.Over.baseChange k K G
  have hGKConnected : ConnectedSpace GK.left := connectedSpace_baseChange_of_connected G K
  -- Local instance justification (proof-local temporary data): connectedness of the chosen base change is used only in the algebraically closed reduction.
  let _ : ConnectedSpace GK.left := hGKConnected
  have hGKJacobson : JacobsonSpace GK.left := hκjac hKjac
  -- Local instance justification (proof-local temporary data): the Jacobson property of the chosen base change is used only in the algebraically closed reduction.
  let _ : JacobsonSpace GK.left := hGKJacobson
  have hGKClosed :
      ∀ x : closedPoints GK.left,
        ∃ g : 𝟙_ (SchemeOverField K) ⟶ GK,
          g.left (IsLocalRing.closedPoint K) = x.1 := by
    intro x
    obtain ⟨gLeft, hgLeft_over, hgLeft_closed⟩ :=
      Scheme.Hom.ResidueField.exists_section_through_closedPoint_of_isAlgClosed
        GK x (hκclosed hKclosed x.1 x.2)
    exact ⟨Over.homMk gLeft hgLeft_over, hgLeft_closed⟩
  have hGKIrreducible : IrreducibleSpace GK.left :=
    irreducibleSpace_of_connected_of_algClosed_of_closedPointsRational GK hGKClosed
  have hGKIrreducible' : IrreducibleSpace (FieldExtension.baseChange k K G.hom) := by
    change IrreducibleSpace GK.left
    exact hGKIrreducible
  -- Local instance justification (proof-local temporary data): irreducibility of the chosen base change is used only by the final descent step.
  let _ : IrreducibleSpace (FieldExtension.baseChange k K G.hom) := hGKIrreducible'
  exact irreducibleSpace_of_irreducible_baseChange (k := k) (K := K) G

/-- The universal subset of a connected group scheme over a field is irreducible. -/
theorem isIrreducible_univ_of_connected
    (G : SchemeOverField k) [GrpObj G] [ConnectedSpace G.left] :
    IsIrreducible (Set.univ : Set G.left) := by
  simpa using IrreducibleSpace.isIrreducible_univ G.left

end AlgebraicGeometry.GroupScheme
