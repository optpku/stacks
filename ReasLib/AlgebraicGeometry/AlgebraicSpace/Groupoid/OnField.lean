module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Groupoids in algebraic spaces on a field

A groupoid in algebraic spaces over `B` is on a field when its object space is
`Spec(k)` for a field `k` over the base scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The object space of a groupoid in algebraic spaces is the spectrum of a field over `S`. -/
class IsOnField {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) : Prop where
  /-- The object space equals `Spec (.of k)` as an algebraic space over `S`. -/
  objectSpace_eq : G.U.left = AlgebraicSpace.ofOver (Over.mk σ)

namespace IsOnField

/-- An equality with the field spectrum makes a groupoid on that field over `S`. -/
theorem of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (h : G.U.left = AlgebraicSpace.ofOver (Over.mk σ)) : IsOnField G σ := sorry

/-- The comparison isomorphism induced by `objectSpace_eq`. -/
def objectSpaceIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ) :=
  eqToIso objectSpace_eq

end IsOnField

/-- Being on a field is equivalent to the object space equalling `Spec (.of k)` over `S`. -/
theorem isOnField_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) :
    IsOnField G σ ↔ G.U.left = AlgebraicSpace.ofOver (Over.mk σ) := sorry

/-- The discrete groupoid on `Spec (.of k)` over `B` is on the field `k`. -/
instance instIsOnField_discrete {S : Scheme.{u}} {B : AlgebraicSpace S} {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) (p : AlgebraicSpace.ofOver (Over.mk σ) ⟶ B) :
    IsOnField (discrete (Over.mk p)) σ := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
