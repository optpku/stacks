/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf

/-!
# Local finite type morphisms from fppf covers

Members of an fppf cover remain locally of finite type after composition with a
locally finite type morphism.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.FppfCover

/-- A member of an fppf cover followed by a locally finite type morphism is locally
of finite type. -/
theorem locallyOfFiniteType_comp {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (𝒰 : FppfCover.{u, v} X) (i : 𝒰.I₀) :
    LocallyOfFiniteType (𝒰.f i ≫ f) := sorry

end AlgebraicGeometry.FppfCover
