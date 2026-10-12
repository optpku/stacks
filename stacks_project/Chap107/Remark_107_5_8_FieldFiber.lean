/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap100.Lemma_100_4_3_Comparison

/-!
# Field-valued 2-fibres of morphisms of algebraic stacks

The fibre of a morphism `f : T ⟶ X` of algebraic stacks over a field-valued
point `p` of `X` is the chosen 2-fibre product `T ×_X Spec(K)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The identity field-valued point of `Spec(K)` over `S` determined by `p`. -/
def FieldValuedPoint.specId {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    FieldValuedPoint (GroupoidsOver.slice p.overObj) :=
  FieldValuedPoint.of p.K p.structureHom (𝟙 (GroupoidsOver.slice p.overObj))

/-- The morphism of `FieldValuedPoint.specId p` is the identity of the slice of
`Spec(K)`. -/
@[simp]
theorem FieldValuedPoint.specId_hom {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    (FieldValuedPoint.specId p).hom = 𝟙 (GroupoidsOver.slice p.overObj) :=
  sorry

/-- The fibre of `f` over a field-valued point `p`, as the 2-fibre product
`T ×_X Spec(K)`. -/
noncomputable def fieldFiber {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom

/-- `fieldFiber f p` is the chosen 2-fibre product of `f` with `p.hom`. -/
theorem fieldFiber_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    fieldFiber f p = TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom :=
  sorry

namespace fieldFiber

/-- The canonical morphism `T ×_X Spec(K) ⟶ T` from the field-valued fibre. -/
def fst {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    fieldFiber f p ⟶ T :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} f p.hom

/-- `fieldFiber.fst f p` is the first projection of the 2-fibre product. -/
theorem fst_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    fst f p = TwoFibreProduct.fst.{u + 1, u, u + 1, u} f p.hom :=
  sorry

/-- The canonical morphism `T ×_X Spec(K) ⟶ Spec(K)` from the field-valued fibre. -/
def snd {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    fieldFiber f p ⟶ GroupoidsOver.slice p.overObj :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f p.hom

/-- `fieldFiber.snd f p` is the second projection of the 2-fibre product. -/
theorem snd_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    snd f p = TwoFibreProduct.snd.{u + 1, u, u + 1, u} f p.hom :=
  sorry

/-- The comparison isomorphism witnessing that the field-valued fibre is
2-commutative. -/
noncomputable def comparisonIso {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    fst f p ≫ f ≅ snd f p ≫ p.hom :=
  TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f p.hom

/-- `fieldFiber.comparisonIso f p` is the comparison isomorphism of the chosen
2-fibre product. -/
theorem comparisonIso_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    comparisonIso f p = TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f p.hom :=
  sorry

/-- The canonical `PseudoPullbackCone` of `f` against `p.hom`. -/
noncomputable def cone {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    PseudoPullbackCone f p.hom :=
  TwoFibreProduct.cone.{u + 1, u, u + 1, u} f p.hom

/-- `fieldFiber.cone f p` is the chosen 2-fibre product cone of `f` against
`p.hom`. -/
theorem cone_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (p : FieldValuedPoint X) :
    cone f p = TwoFibreProduct.cone.{u + 1, u, u + 1, u} f p.hom :=
  sorry

/-- A point of `|T|` lying over `Points.mk p` lifts to a point of the field fibre
`T ×_X Spec(K)`. -/
theorem exists_lift {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] (f : T ⟶ X) (t : Points T)
    (p : FieldValuedPoint X) (hp : Points.mk p = Points.map f t)
    [AlgebraicStack (fieldFiber f p)] :
    ∃ t' : Points (fieldFiber f p),
      Points.map (fst f p) t' = t ∧
        Points.map (snd f p) t' = Points.mk (FieldValuedPoint.specId p) :=
  sorry

end fieldFiber

end AlgebraicGeometry.AlgebraicStack
