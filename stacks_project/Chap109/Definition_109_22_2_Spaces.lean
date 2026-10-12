/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Definition_109_21_2_Spaces
public import stacks_project.Chap109.Definition_109_22_2_Family

/-!
# Stable morphisms of algebraic spaces

A morphism of algebraic spaces is a stable family of curves when it is
prestable and every field-valued fibre is a scheme of genus at least two with
neither a rational tail nor a rational bridge.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Being a stable fibre is independent of the chosen representing scheme of an
algebraic-space fibre. -/
theorem ofFibreScheme_isStableFibre_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (p : FieldValuedPoint Y)
    (T T' : Over S) (e : fieldFiber f p ≅ ofOver T)
    (e' : fieldFiber f p ≅ ofOver T') :
    IsStableFibre (ofFibreScheme p T e) ↔
      IsStableFibre (ofFibreScheme p T' e') :=
  sorry

/-- A morphism of algebraic spaces is a stable family if it is prestable and every
field-valued fibre is a scheme which, under any representing isomorphism, is a
stable fibre. -/
@[mk_iff]
class IsStableFamily {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends Prestable f where
  /-- Every field-valued fibre is a scheme. -/
  fibre_isScheme : ∀ p : FieldValuedPoint Y, IsScheme (fieldFiber f p)
  /-- Every representing scheme of a field-valued fibre is a stable fibre. -/
  fibres_stable :
    ∀ (p : FieldValuedPoint Y) (T : Over S) (e : fieldFiber f p ≅ ofOver T),
      IsStableFibre (ofFibreScheme p T e)

namespace IsStableFamily

/-- A stable family of algebraic spaces is prestable. -/
instance instPrestable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : IsStableFamily f] : Prestable f :=
  h.toPrestable

/-- A stable family of algebraic spaces is at-worst-nodal of relative
dimension one. -/
instance instAtWorstNodal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : IsStableFamily f] : AtWorstNodal f :=
  h.toAtWorstNodal

/-- A stable family of algebraic spaces is semistable. -/
instance instSemistable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsStableFamily f] : Semistable f :=
  sorry

/-- A stable family of algebraic spaces is prestable, every field-valued
fibre is a scheme, and every representing scheme of such a fibre is a stable
fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsStableFamily f] :
    Prestable f ∧ (∀ p : FieldValuedPoint Y, IsScheme (fieldFiber f p)) ∧
      ∀ (p : FieldValuedPoint Y) (T : Over S)
        (e : fieldFiber f p ≅ ofOver T),
        IsStableFibre (ofFibreScheme p T e) :=
  sorry

end IsStableFamily

/-- A stable family of schemes over `S` remains a stable family as a morphism of
algebraic spaces via `ofOverMap`. -/
instance instIsStableFamily_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.IsStableFamily h.left] : IsStableFamily (ofOverMap h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of stable families of curves. -/
def stable (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ IsStableFamily (hom P)

/-- Membership in `stable` is that the structure morphism is a stable family. -/
theorem stable_iff {S : Scheme.{u}} (P : Obj S) :
    stable S P ↔ IsStableFamily (hom P) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
