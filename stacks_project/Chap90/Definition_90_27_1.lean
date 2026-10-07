module

public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Definition_90_27_1_GroupoidInFunctors
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Definition_90_27_1_Quotient

/-!
# Normalized and minimal smooth prorepresentable groupoids in functors

A smooth prorepresentable groupoid in functors on `C_Λ` is normalized when its fibre
groupoid at the dual numbers is totally disconnected, and minimal when the quotient
morphism `U ⟶ [U/R]` is given by a minimal versal formal object of `[U/R]`.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Definition 90.27.1 (1): a smooth prorepresentable groupoid in functors
`(U, R, s, t, c)` on `ArtinianLocalAlgCat Λ k` is normalized if the fibre groupoid
`(U(k[ε]), R(k[ε]), s, t, c)` is totally disconnected, equivalently if
`s.app (dualNumber Λ k) = t.app (dualNumber Λ k)`. -/
@[stacks 06KM]
class IsNormalized (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] : Prop where
  /-- Source and target agree on the dual-number fibre. -/
  source_eq_target_dualNumber :
    G.s.app (dualNumber Λ k) = G.t.app (dualNumber Λ k)

/-- Normalization is equality of source and target on `dualNumber Λ k`. -/
theorem IsNormalized.spec (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsNormalized G] :
    G.s.app (dualNumber Λ k) = G.t.app (dualNumber Λ k) :=
  sorry

/-- A smooth prorepresentable groupoid in functors is normalized if and only if
the fibre groupoid at `dualNumber Λ k` has no morphisms between distinct objects. -/
theorem IsNormalized.iff_totallyDisconnected
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    IsNormalized G ↔
      ∀ (x y : G.U.obj (dualNumber Λ k)),
        x ≠ y → IsEmpty (G.PointHom (dualNumber Λ k) x y) :=
  sorry

/-- Definition 90.27.1 (2): a smooth prorepresentable groupoid in functors
`(U, R, s, t, c)` on `ArtinianLocalAlgCat Λ k` is minimal if the quotient morphism
`U ⟶ [U/R]` is given by a minimal versal formal object of `[U/R]`. -/
@[stacks 06KM]
class IsMinimal (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] : Prop where
  /-- For every prorepresentation of `U`, the associated formal object of `[U/R]` is
  minimal versal. -/
  of_prorepresentation :
    ∀ {R : CompleteLocalAlgCat Λ k}
      (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R),
      (G.quotientFormalObject e).IsMinimalVersal

/-- For a minimal groupoid, morphisms of formal objects into `quotientFormalObject e`
are surjective on complete local bases. -/
theorem IsMinimal.spec (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R)
    {η : FormalObject G.forgetULift} (f : η ⟶ G.quotientFormalObject e) :
    Function.Surjective f.base.hom :=
  sorry

/-- Minimality means that `quotientFormalObject e` is a minimal versal formal
object of `[U/R]` for every prorepresentation `e` of `U`. -/
instance instIsMinimalVersal_quotientFormalObject
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [h : IsMinimal G]
    {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    (G.quotientFormalObject e).IsMinimalVersal :=
  h.of_prorepresentation e

/-- The discrete groupoid on a restricted coyoneda functor is normalized. -/
@[stacks 06KM, instance]
instance instIsNormalizedDiscrete (R : CompleteLocalAlgCat Λ k) :
    IsNormalized (discrete (CompleteLocalAlgCat.restrictedCoyoneda R)) where
  source_eq_target_dualNumber := rfl

/-- The discrete groupoid on a restricted coyoneda functor is minimal. -/
@[stacks 06KM, instance]
instance instIsMinimalDiscrete (R : CompleteLocalAlgCat Λ k) :
    IsMinimal (discrete (CompleteLocalAlgCat.restrictedCoyoneda R)) :=
  sorry

end CategoryTheory.GroupoidInFunctors

