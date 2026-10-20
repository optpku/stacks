/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Quasi-separatedness for locally finite type morphisms

A morphism locally of finite type over a locally Noetherian scheme is quasi-separated.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism locally of finite type over a locally Noetherian scheme is quasi-separated. -/
theorem quasiSeparated_of_locallyOfFiniteType
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    QuasiSeparated f := by
  exact @QuasiSeparated.of_quasiSeparatedSpace X S f
    (@IsLocallyNoetherian.quasiSeparatedSpace X
      (LocallyOfFiniteType.isLocallyNoetherian f))

/-- A locally finite type morphism over a locally Noetherian scheme is inferred to be
quasi-separated. -/
instance (priority := low) instQuasiSeparatedOfLocallyOfFiniteType
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    QuasiSeparated f :=
  quasiSeparated_of_locallyOfFiniteType f

end AlgebraicGeometry
