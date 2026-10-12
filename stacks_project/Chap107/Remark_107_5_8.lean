/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Remark_107_5_8_FieldFiber

/-!
# Well-definedness of relative dimension of algebraic stacks

The quantity `dimensionAt` of a field-valued 2-fibre of a locally of finite
type morphism of locally Noetherian algebraic stacks is independent of the
chosen field-valued representative of the image point and of the chosen lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Remark 107.5.8: for a locally of finite type morphism `f : T ⟶ X` of locally
Noetherian algebraic stacks and a point `t` of `|T|`, the value
`dimensionAt t'` of any lift of `t` to `fieldFiber f p` is independent of the
`FieldValuedPoint` representative `p` of `Points.map f t` and of the chosen
lift `t'`. -/
@[stacks 0DRM]
theorem dimensionAt_fieldFiber_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T)
    {p q : FieldValuedPoint X}
    (hp : Points.mk p = Points.map f t)
    (hq : Points.mk q = Points.map f t)
    [AlgebraicStack (fieldFiber f p)] [AlgebraicStack (fieldFiber f q)]
    [IsLocallyNoetherian (fieldFiber f p)]
    [IsLocallyNoetherian (fieldFiber f q)]
    {t' : Points (fieldFiber f p)} {t'' : Points (fieldFiber f q)}
    (ht' : Points.map (fieldFiber.fst f p) t' = t)
    (ht'' : Points.map (fieldFiber.fst f q) t'' = t) :
    dimensionAt t' = dimensionAt t'' :=
  sorry

/-- The dimension at a point of a field-valued 2-fibre of `f` is independent of
the chosen field-valued representative of `Points.map f t` and of the chosen
bilimit cone and lift. -/
theorem dimensionAt_fieldFiber_eq_of_isBilimit {S : Scheme.{u}}
    {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T)
    {p q : FieldValuedPoint X}
    (hp : Points.mk p = Points.map f t)
    (hq : Points.mk q = Points.map f t)
    (c : PseudoPullbackCone f p.hom) (d : PseudoPullbackCone f q.hom)
    [AlgebraicStack c.pt] [AlgebraicStack d.pt]
    [IsLocallyNoetherian c.pt] [IsLocallyNoetherian d.pt]
    (hc : c.IsBilimit) (hd : d.IsBilimit)
    {t' : Points c.pt} {t'' : Points d.pt}
    (ht' : Points.map c.fst t' = t) (ht'' : Points.map d.fst t'' = t) :
    dimensionAt t' = dimensionAt t'' :=
  sorry

end AlgebraicGeometry.AlgebraicStack
