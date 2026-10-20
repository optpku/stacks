/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation morphisms into Noetherian algebraic spaces

A morphism of algebraic spaces of finite presentation into a Noetherian
target has Noetherian source.
Over a locally Noetherian target, locally finite type morphisms are locally of
finite presentation, and quasi-separated finite type morphisms are of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePresentation

/-- A morphism of algebraic spaces over a scheme that is of finite presentation
and has Noetherian target has Noetherian source. -/
@[stacks 04ZL]
theorem isNoetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FinitePresentation f] [IsNoetherian Y] :
    IsNoetherian X :=
  sorry

end FinitePresentation

/-- A morphism of algebraic spaces which is locally of finite type, with
locally Noetherian target, is locally of finite presentation. -/
@[stacks 06G4]
instance locallyOfFinitePresentation_of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] : LocallyOfFinitePresentation f :=
  sorry

/-- A morphism of algebraic spaces which is of finite type and quasi-separated,
with locally Noetherian target, is of finite presentation. -/
@[stacks 06G4]
instance finitePresentation_of_finiteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [FiniteType f] [QuasiSeparated f] : FinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
