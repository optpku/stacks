/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.LocallyOfFiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation over a locally Noetherian base

Over a locally Noetherian base scheme, a finite type morphism is of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite type morphism over a locally Noetherian base is of finite presentation. -/
@[stacks 01TX]
theorem finitePresentation_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [FiniteType f] [IsLocallyNoetherian S] :
    FinitePresentation f := by
  exact {
    toLocallyOfFinitePresentation :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    toQuasiCompact := inferInstance
    toQuasiSeparated := AlgebraicGeometry.quasiSeparated_of_locallyOfFiniteType f }

end AlgebraicGeometry.Scheme.Hom
