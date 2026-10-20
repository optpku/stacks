module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Conormal

@[expose] public section

open IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A point is a split node when it is nodal, has the same residue field as the base,
and its cotangent relation splits into two coordinate directions. -/
def isSplitNodeAt {k : Type u} [Field k] (X : SchemeOverField k) (x : X.left) : Prop :=
  let A := stalkRing X x
  let κ := ResidueField A
  let V := CotangentSpace A
  isNode X x ∧
    Function.Bijective (algebraMap k κ) ∧
      ∃ e : Module.Basis (Fin 2) κ V,
        idealConormalAlgebraQuotient (maximalIdeal A)
          (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) = 0

/-- The pointwise split-node predicate is equivalent to its defining nodality, residue-field,
and cotangent-relation conditions. -/
theorem isSplitNodeAt_iff {k : Type u} [Field k] (X : SchemeOverField k) (x : X.left) :
    isSplitNodeAt X x ↔
      let A := stalkRing X x
      let κ := ResidueField A
      let V := CotangentSpace A
      isNode X x ∧
        Function.Bijective (algebraMap k κ) ∧
          ∃ e : Module.Basis (Fin 2) κ V,
            idealConormalAlgebraQuotient (maximalIdeal A)
              (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) = 0 := sorry

/-- A split node is a nodal point with trivial residue-field extension and split quadratic
cotangent relation. -/
def isSplitNode {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (h_dimension : topologicalKrullDim X.left = 1) (x : X.left) : Prop :=
  isSplitNodeAt X x

/-- The split-node predicate is equivalent to its nodality, residue-field, and cotangent-relation
components. -/
theorem isSplitNode_iff {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (h_dimension : topologicalKrullDim X.left = 1) (x : X.left) :
    isSplitNode X h_dimension x ↔
      let A := stalkRing X x
      let κ := ResidueField A
      let V := CotangentSpace A
      isNode X x ∧
        Function.Bijective (algebraMap k κ) ∧
          ∃ e : Module.Basis (Fin 2) κ V,
            idealConormalAlgebraQuotient (maximalIdeal A)
              (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) = 0 := sorry

/-- A split node is a node. -/
theorem isSplitNode.isNode {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (h_dimension : topologicalKrullDim X.left = 1) (x : X.left)
    (h : isSplitNode X h_dimension x) : isNode X x := sorry

/-- At a split node, the canonical map from the base field to the residue field is bijective. -/
theorem isSplitNode.residueField_bijective {k : Type u} [Field k]
    (X : SchemeOverField k) [Algebraic X] (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h : isSplitNode X h_dimension x) :
    Function.Bijective (algebraMap k (ResidueField (stalkRing X x))) := sorry

/-- At a split node, the cotangent space has a basis whose coordinate relation is `xy`. -/
theorem isSplitNode.quadraticRelation {k : Type u} [Field k] (X : SchemeOverField k)
    [Algebraic X] (h_dimension : topologicalKrullDim X.left = 1) (x : X.left)
    (h : isSplitNode X h_dimension x) :
    ∃ e : Module.Basis (Fin 2) (ResidueField (stalkRing X x))
        (CotangentSpace (stalkRing X x)),
      idealConormalAlgebraQuotient (maximalIdeal (stalkRing X x))
          (SymmetricAlgebra.ι (ResidueField (stalkRing X x))
              (CotangentSpace (stalkRing X x)) (e 0) *
            SymmetricAlgebra.ι (ResidueField (stalkRing X x))
              (CotangentSpace (stalkRing X x)) (e 1)) = 0 := sorry

end AlgebraicGeometry.SchemeOverField
