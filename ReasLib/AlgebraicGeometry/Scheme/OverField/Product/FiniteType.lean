/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite product of schemes locally of finite type over a field remains locally of finite
type over that field. -/
instance locallyOfFiniteType_pi {k : Type u} [Field k] {n : ℕ}
    (C : Fin n → SchemeOverField k) [∀ i, LocallyOfFiniteType (C i).hom] :
    LocallyOfFiniteType (∏ᶜ C).hom := sorry

end AlgebraicGeometry
