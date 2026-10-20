/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeOver

variable {S : Scheme.{u}} [IsNoetherian S]

/-- The identity structure morphism of a scheme is finite type. -/
theorem baseFiniteType (S : Scheme.{u}) : Hom.FiniteType (Over.mk (𝟙 S)).hom := sorry

/-- The base scheme regarded as a finite-type scheme over itself. -/
def base (S : Scheme.{u}) [IsNoetherian S] : FiniteTypeOver S :=
  ⟨Over.mk (𝟙 S), baseFiniteType S⟩

/-- The structure morphism from a finite-type scheme to its base object. -/
def toBase (X : FiniteTypeOver S) : X ⟶ base S :=
  ObjectProperty.homMk (Over.homMk X.obj.hom)

/-- The underlying map of `toBase X` is the structure morphism of `X`. -/
theorem toBase_hom (X : FiniteTypeOver S) :
    (toBase X).hom.left = X.obj.hom := sorry

end AlgebraicGeometry.Scheme.FiniteTypeOver
