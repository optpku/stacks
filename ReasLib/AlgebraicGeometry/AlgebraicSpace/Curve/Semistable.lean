module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Curve.StableCurves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Semistable

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
          (e.inv ≫ fieldFiberToSpec f p :
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

/-- A proper semistable morphism of schemes over `S` is a semistable family
of algebraic spaces via `ofOverMap`. Properness is required in addition to the
generalized scheme semistability predicate. -/
instance instSemistable_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Semistable h.left] [IsProper h.left] :
    Semistable (ofOverMap h) :=
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
