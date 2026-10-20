module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Nodal families of curves

The nodal condition on a family of curves is represented by an open of its
base under arbitrary scheme base change. Over a field it is characterized by
at-worst-nodal singularities and dimension one of every irreducible component.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves that are at-worst-nodal of
relative dimension one. -/
def nodal (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.AtWorstNodal (hom P)

/-- Membership in the nodal object property is at-worst-nodality of the
structure morphism. -/
theorem nodal_iff {S : Scheme.{u}} (P : Obj S) :
    nodal S P ↔ AlgebraicSpace.AtWorstNodal (hom P) := Iff.rfl

/-- The at-worst-nodal property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_nodal (S : Scheme.{u}) :
    (nodal S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents the condition
that its pullback is at-worst-nodal of relative dimension one under every
scheme base change. -/
theorem exists_nodal_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      AlgebraicSpace.AtWorstNodal
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ↔
        Set.range T.hom ⊆ U :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a nodal
curve family precisely when its singularities are at-worst-nodal and each
irreducible component has dimension one. -/
theorem nodal_iff_scheme_components
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    nodal (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∀ Z : irreducibleComponents X.left,
          topologicalKrullDim Z = 1 :=
  sorry

/-- A nonempty proper scheme of dimension at most one over a field defines a
nodal curve family precisely when its singularities are at-worst-nodal and it
is equidimensional of dimension one. -/
theorem classifying_factorsThrough_nodal_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    nodal (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
