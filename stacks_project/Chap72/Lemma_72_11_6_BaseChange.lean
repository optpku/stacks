/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Points of a field-extension base change of an algebraic space

A field-valued point of the base change of an algebraic space `X` over `k` along
`specMap k k'` determines a field-valued point of `X` with the same source field,
by postcomposing the structure morphism with `specMap k k'` and transporting the
Yoneda section along `baseChangePresheaf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat Opposite
open AlgebraicGeometry.FieldExtension (specMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

/-- The field-valued point of `X` obtained from a field-valued point of the
base change of `X` along `specMap k k'`, by viewing `Spec(K)` over `Spec k`. -/
def fieldValuedPointToSource {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : AlgebraicSpace (Spec (of k))}
    (p : FieldValuedPoint (baseChange (specMap k k') X)) :
    FieldValuedPoint X where
  K := p.K
  field := p.field
  structureHom := p.structureHom ≫ specMap k k'
  hom :=
    (yonedaEquiv.symm
        (p.elem :
          X.functorOfPoints.obj (op (Over.mk (p.structureHom ≫ specMap k k')))) :
      ofOver (Over.mk (p.structureHom ≫ specMap k k')) ⟶ X)

/-- The structure morphism of `fieldValuedPointToSource p` is `p.structureHom`
postcomposed with `specMap k k'`. -/
@[simp]
theorem fieldValuedPointToSource_structureHom {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] {X : AlgebraicSpace (Spec (of k))}
    (p : FieldValuedPoint (baseChange (specMap k k') X)) :
    (fieldValuedPointToSource p).structureHom = p.structureHom ≫ specMap k k' :=
  sorry

/-- Equivalence of field-valued points of the field-extension base change is
preserved by `fieldValuedPointToSource`. -/
theorem fieldValuedPointToSource_equivalent {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] {X : AlgebraicSpace (Spec (of k))}
    {p q : FieldValuedPoint (baseChange (specMap k k') X)}
    (h : FieldValuedPoint.Equivalent p q) :
    FieldValuedPoint.Equivalent (fieldValuedPointToSource p) (fieldValuedPointToSource q) :=
  sorry

/-- The map `|X_{k'}| → |X|` sending a point of the field-extension base change
to the point of `X` it lies over. -/
def toSourceOnPoints (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (of k))) :
    Points (baseChange (specMap k k') X) → Points X :=
  Quotient.map fieldValuedPointToSource fun _ _ h ↦
    fieldValuedPointToSource_equivalent h

/-- `toSourceOnPoints` sends the class of a field-valued point to the class of
`fieldValuedPointToSource`. -/
@[simp]
theorem toSourceOnPoints_mk {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : AlgebraicSpace (Spec (of k))}
    (p : FieldValuedPoint (baseChange (specMap k k') X)) :
    toSourceOnPoints k k' X (Points.mk p) = Points.mk (fieldValuedPointToSource p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FieldExtension
