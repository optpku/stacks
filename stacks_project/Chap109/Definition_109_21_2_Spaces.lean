/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap99.Situation_99_15_1_Category
public import stacks_project.Chap109.Definition_109_20_1_Prestable
public import stacks_project.Chap109.Definition_109_21_2_Semistable

/-!
# Semistable morphisms of algebraic spaces

A morphism of algebraic spaces is a semistable family of curves when it is
prestable and every field-valued fibre is a scheme of genus at least one with
no rational tail.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Convert a representing scheme of an algebraic-space fibre over a
field-valued point into a scheme over that field. -/
def ofFibreScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FieldValuedPoint Y) (T : Over S) (e : fieldFiber f p ≅ ofOver T) :
    SchemeOverField p.K :=
  Over.mk
    (yonedaEquiv
        (e.inv ≫ fiberToSpec f p : yoneda.obj T ⟶ yoneda.obj p.overObj)).left

/-- The underlying scheme of `ofFibreScheme p T e` is the representing scheme
`T`. -/
theorem ofFibreScheme_left {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (p : FieldValuedPoint Y) (T : Over S)
    (e : fieldFiber f p ≅ ofOver T) :
    (ofFibreScheme p T e).left = T.left :=
  sorry

/-- The structure morphism of `ofFibreScheme p T e` is the scheme morphism
underlying the comparison of `T` with `Spec(p.K)` over `S`. -/
theorem ofFibreScheme_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (p : FieldValuedPoint Y) (T : Over S)
    (e : fieldFiber f p ≅ ofOver T) :
    (ofFibreScheme p T e).hom =
      (yonedaEquiv
          (e.inv ≫ fiberToSpec f p :
            yoneda.obj T ⟶ yoneda.obj p.overObj)).left :=
  sorry

/-- Being a semistable fibre is independent of the chosen representing scheme
of an algebraic-space fibre. -/
theorem ofFibreScheme_isSemistableFibre_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (p : FieldValuedPoint Y)
    (T T' : Over S) (e : fieldFiber f p ≅ ofOver T)
    (e' : fieldFiber f p ≅ ofOver T') :
    IsSemistableFibre (ofFibreScheme p T e) ↔
      IsSemistableFibre (ofFibreScheme p T' e') :=
  sorry

/-- A morphism of algebraic spaces is semistable if it is prestable and every
field-valued fibre is a scheme which, under any representing isomorphism, is a
semistable fibre. -/
@[mk_iff]
class Semistable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends Prestable f where
  /-- Every field-valued fibre is a scheme. -/
  fibre_isScheme : ∀ p : FieldValuedPoint Y, IsScheme (fieldFiber f p)
  /-- Every representing scheme of a field-valued fibre is a semistable
  fibre. -/
  fibres_semistable :
    ∀ (p : FieldValuedPoint Y) (T : Over S) (e : fieldFiber f p ≅ ofOver T),
      IsSemistableFibre (ofFibreScheme p T e)

namespace Semistable

/-- A semistable morphism of algebraic spaces is prestable. -/
instance instPrestable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : Semistable f] : Prestable f :=
  h.toPrestable

/-- A semistable morphism of algebraic spaces is at-worst-nodal of relative
dimension one. -/
instance instAtWorstNodal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : Semistable f] : AtWorstNodal f :=
  h.toAtWorstNodal

/-- A semistable morphism of algebraic spaces is prestable, every field-valued
fibre is a scheme, and every representing scheme of such a fibre is a
semistable fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Semistable f] :
    Prestable f ∧ (∀ p : FieldValuedPoint Y, IsScheme (fieldFiber f p)) ∧
      ∀ (p : FieldValuedPoint Y) (T : Over S)
        (e : fieldFiber f p ≅ ofOver T),
        IsSemistableFibre (ofFibreScheme p T e) :=
  sorry

end Semistable

/-- A semistable morphism of schemes over `S` remains semistable as a morphism
of algebraic spaces via `ofOverMap`. -/
instance instSemistable_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Semistable h.left] : Semistable (ofOverMap h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of semistable families of curves. -/
def semistable (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ Semistable (hom P)

/-- Membership in `semistable` is semistability of the structure morphism. -/
theorem semistable_iff {S : Scheme.{u}} (P : Obj S) :
    semistable S P ↔ Semistable (hom P) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
