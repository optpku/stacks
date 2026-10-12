/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpreadingOut
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A locally finite type morphism whose stalk map is an isomorphism restricts to an open
immersion near the source point when the target germ is injective there. -/
theorem exists_open_neighborhood_isOpenImmersion_of_stalkMap_isIso
    [LocallyOfFiniteType f] (x : X) [S.IsGermInjectiveAt (f x)] [IsIso (f.stalkMap x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := sorry

/-- A finite type morphism to a reduced scheme with finitely many irreducible components whose
stalk map is an isomorphism restricts to an open immersion near the source point. -/
@[stacks 09NH]
theorem exists_openImmersion_neighborhood_of_stalkMap_isIso
    [FiniteType f] [IsReduced S] [Finite (irreducibleComponents S)]
    (x : X) [IsIso (f.stalkMap x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := sorry

end Scheme.Hom
end AlgebraicGeometry
