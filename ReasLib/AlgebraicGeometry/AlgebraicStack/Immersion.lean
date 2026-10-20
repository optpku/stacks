/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Base change of immersions of algebraic stacks

Immersions, closed immersions, and open immersions of algebraic stacks are
stable under arbitrary two-fibre-product base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Immersion

/-- The second projection of the two-fibre product of an immersion of algebraic
stacks with an arbitrary morphism of algebraic stacks is an immersion. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [Immersion i] :
    Immersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f) :=
  sorry

end Immersion

namespace ClosedImmersion

/-- The second projection of the two-fibre product of a closed immersion of
algebraic stacks with an arbitrary morphism of algebraic stacks is a closed
immersion. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [ClosedImmersion i] :
    ClosedImmersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f) :=
  sorry

end ClosedImmersion

namespace OpenImmersion

/-- The second projection of the two-fibre product of an open immersion of
algebraic stacks with an arbitrary morphism of algebraic stacks is an open
immersion. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [OpenImmersion i] :
    OpenImmersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f) :=
  sorry

end OpenImmersion

end AlgebraicGeometry.Groupoids.Hom
