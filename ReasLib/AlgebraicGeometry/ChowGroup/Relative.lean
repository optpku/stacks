/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The degree-`k` Chow group of a scheme locally of finite type over a universally catenary
scheme, graded by the relative dimension function induced from the base. -/
abbrev RelativeChow
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ) :=
  @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    (X.hom.relativeDimensionFunction delta) inferInstance k

end AlgebraicGeometry
