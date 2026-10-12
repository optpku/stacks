/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver.Base

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

variable {S : Scheme.{u}} [IsNoetherian S]

/-- Forget separatedness and retain only finite type over the base. -/
def toFiniteTypeOver (X : FiniteTypeSeparatedOver S) : FiniteTypeOver S :=
  ⟨X.obj, X.property.2⟩

/-- A morphism of separated finite-type schemes, regarded as a finite-type morphism. -/
def homToFiniteTypeOver {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    toFiniteTypeOver X ⟶ toFiniteTypeOver Y := ObjectProperty.homMk f.hom

/-- The underlying map of `homToFiniteTypeOver f` equals `f.hom`. -/
theorem homToFiniteTypeOver_hom {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    (homToFiniteTypeOver f).hom = f.hom := sorry

/-- The identity structure morphism of the base scheme is separated. -/
theorem baseSeparated (S : Scheme.{u}) : IsSeparated (Over.mk (𝟙 S)).hom := sorry

/-- The base scheme regarded as separated and finite type over itself. -/
def base (S : Scheme.{u}) [IsNoetherian S] : FiniteTypeSeparatedOver S :=
  ⟨Over.mk (𝟙 S), baseSeparated S, FiniteTypeOver.baseFiniteType S⟩

/-- The structure morphism from a separated finite-type scheme to its base object. -/
def toBase (X : FiniteTypeSeparatedOver S) : X ⟶ base S :=
  ObjectProperty.homMk (Over.homMk X.obj.hom)

end AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
