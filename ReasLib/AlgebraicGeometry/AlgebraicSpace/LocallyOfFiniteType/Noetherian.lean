/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally of finite type over locally Noetherian algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- A locally-of-finite-type morphism of algebraic spaces over a scheme with
locally Noetherian target has locally Noetherian source. -/
@[stacks 04ZK]
theorem isLocallyNoetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  sorry

end LocallyOfFiniteType

/-- An algebraic space locally of finite type over a locally Noetherian scheme is
locally Noetherian via its unique structure morphism. -/
instance instIsLocallyNoetherian_of_locallyOfFiniteType_toBase
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (X : AlgebraicSpace S) [LocallyOfFiniteType (SchemeRealization.toBase X)] :
    IsLocallyNoetherian X :=
  @LocallyOfFiniteType.isLocallyNoetherian S X (ofOver (Over.mk (𝟙 S)))
    (SchemeRealization.toBase X) inferInstance
    (@instIsLocallyNoetherian_ofOver S (Over.mk (𝟙 S))
      (inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian S)))

end AlgebraicGeometry.AlgebraicSpace
