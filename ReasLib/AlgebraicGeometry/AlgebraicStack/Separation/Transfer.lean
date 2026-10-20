/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Composition

/-!
# Transfer of separation axioms along morphisms of algebraic stacks

If a morphism of algebraic stacks is DM, quasi-DM, separated, or
quasi-separated, then the corresponding relative and absolute separation
axioms pass from the target to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source of a DM morphism to an algebraic stack that is
DM over the base scheme is DM over the base scheme. -/
@[stacks 050L]
theorem IsDMOver.of_DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsDMOver Y] [DM f] :
    IsDMOver X :=
  sorry

/-- The source of a quasi-DM morphism to an algebraic stack that is
quasi-DM over the base scheme is quasi-DM over the base scheme. -/
@[stacks 050L]
theorem IsQuasiDMOver.of_quasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsQuasiDMOver Y]
    [QuasiDM f] : IsQuasiDMOver X :=
  sorry

/-- The source of a separated morphism to an algebraic stack that is
separated over the base scheme is separated over the base scheme. -/
@[stacks 050L]
theorem IsSeparatedOver.of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsSeparatedOver Y]
    [Separated f] : IsSeparatedOver X :=
  sorry

/-- The source of a quasi-separated morphism to an algebraic stack that is
quasi-separated over the base scheme is quasi-separated over the base scheme. -/
@[stacks 050L]
theorem IsQuasiSeparatedOver.of_quasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparatedOver Y] [QuasiSeparated f] : IsQuasiSeparatedOver X :=
  sorry

/-- The source of a DM morphism to an algebraic stack that is
DM is DM. -/
@[stacks 050L]
theorem IsDM.of_DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsDM Y] [DM f] :
    IsDM X :=
  sorry

/-- The source of a quasi-DM morphism to an algebraic stack that is
quasi-DM is quasi-DM. -/
@[stacks 050L]
theorem IsQuasiDM.of_quasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsQuasiDM Y]
    [QuasiDM f] : IsQuasiDM X :=
  sorry

/-- The source of a separated morphism to an algebraic stack that is
separated is separated. -/
@[stacks 050L]
theorem IsSeparated.of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsSeparated Y]
    [Separated f] : IsSeparated X :=
  sorry

/-- The source of a quasi-separated morphism to an algebraic stack that is
quasi-separated is quasi-separated. -/
@[stacks 050L]
theorem IsQuasiSeparated.of_quasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparated Y] [QuasiSeparated f] : IsQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
