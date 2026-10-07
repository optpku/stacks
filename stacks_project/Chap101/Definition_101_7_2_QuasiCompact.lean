module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact

/-!
# Quasi-compact morphisms of algebraic stacks

A morphism of algebraic stacks is quasi-compact when every 2-fibre product
against a morphism from a quasi-compact algebraic stack remains a
quasi-compact algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is quasi-compact if
for every quasi-compact algebraic stack `Z` and morphism `g : Z ⟶ Y`, every
2-fibre product of `f` against `g` is a quasi-compact algebraic stack.

The Stacks source writes the fibre product as `Z ×_Y X`; the Lean test uses a
`PseudoPullbackCone f g`, whose first projection lands in `X` and whose second
projection lands in `Z`. -/
@[mk_iff]
class QuasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The apex of a bilimit `PseudoPullbackCone` for `f` is quasi-compact
  whenever the test object is a quasi-compact algebraic stack. -/
  pullback_isQuasiCompact {Z : GroupoidsOver S} {g : Z ⟶ Y} [AlgebraicStack Z]
    [IsQuasiCompact Z] (c : PseudoPullbackCone f g) [AlgebraicStack c.pt]
    (hc : c.IsBilimit) : IsQuasiCompact c.pt

namespace QuasiCompact

/-- The identity morphism of an algebraic stack is quasi-compact. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    QuasiCompact (𝟙 X) := sorry

/-- An isomorphism of algebraic stacks is quasi-compact. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := sorry

/-- A quasi-compact morphism pulls quasi-compact algebraic stacks back to
quasi-compact algebraic stacks along any bilimit 2-fibre product cone. -/
theorem spec {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} [QuasiCompact f] {g : Z ⟶ Y} [IsQuasiCompact Z]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsQuasiCompact c.pt := sorry

/-- The source of a quasi-compact morphism is quasi-compact whenever the
target is quasi-compact. -/
theorem isQuasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f] [IsQuasiCompact Y] : IsQuasiCompact X := sorry

end QuasiCompact

/-- The chosen 2-fibre product of a quasi-compact morphism with a morphism from
a quasi-compact algebraic stack is quasi-compact, once the apex is known to be
an algebraic stack. -/
instance instIsQuasiCompact_twoFibreProduct {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiCompact f]
    [IsQuasiCompact Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsQuasiCompact (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack
