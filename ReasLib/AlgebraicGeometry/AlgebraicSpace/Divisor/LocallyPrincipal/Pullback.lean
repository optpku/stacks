/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-!
# Pullbacks of locally principal closed subspaces

Local principality of a closed immersion of algebraic spaces is stable under
arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal

/-- Local principality of a closed immersion of algebraic spaces is preserved by
the first leg of an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {P X' X Z : AlgebraicSpace S}
    {f : X' ⟶ X} {i : Z ⟶ X} {p : P ⟶ X'} {q : P ⟶ Z}
    (sq : IsPullback p q f i) [IsLocallyPrincipal i] :
    IsLocallyPrincipal p :=
  sorry

/-- The inverse-image inclusion of a locally principal closed subspace along a
morphism of algebraic spaces is locally principal. -/
instance inverseImageι {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyPrincipal i] :
    IsLocallyPrincipal (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i) :=
  of_isPullback (AlgebraicGeometry.AlgebraicSpace.inverseImage_isPullback f i)

/-- The first projection from the pullback of a locally principal closed immersion
of algebraic spaces is locally principal. -/
instance pullback_fst {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyPrincipal i] :
    IsLocallyPrincipal (pullback.fst f i) :=
  of_isPullback (CategoryTheory.IsPullback.of_hasPullback f i)

end AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal
