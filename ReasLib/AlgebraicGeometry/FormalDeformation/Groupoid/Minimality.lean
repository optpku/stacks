module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Quotient
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Normalized and minimal presentations by groupoids in functors

Normalization is equality of the dual-number source and target maps. Minimality
means that the actual quotient presentation is given by a minimal versal object.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Source and target maps are normalized when they agree on the dual-number fibre. -/
class IsNormalizedMaps {U R : ArtinianLocalAlgCat Λ k ⥤ Type u} (s t : R ⟶ U) : Prop where
  /-- Source and target agree on the dual-number fibre. -/
  source_eq_target_dualNumber : s.app (dualNumber Λ k) = t.app (dualNumber Λ k)

/-- A smooth prorepresentable groupoid is normalized when source and target agree on dual numbers. -/
abbrev IsNormalized (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [smooth : IsSmooth G.s G.t] [prorepresentable : IsProrepresentable G] : Prop := IsNormalizedMaps G.s G.t

/-- Normalization gives equality of source and target on the dual-number fibre. -/
theorem IsNormalized.spec (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [normalized : IsNormalized G] :
    G.s.app (dualNumber Λ k) = G.t.app (dualNumber Λ k) :=
  normalized.source_eq_target_dualNumber

/-- Normalization is equivalent to absence of arrows between distinct dual-number points. -/
theorem IsNormalized.iff_totallyDisconnected
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    IsNormalized G ↔ ∀ (x y : G.U.obj (dualNumber Λ k)),
      x ≠ y → IsEmpty (G.PointHom (dualNumber Λ k) x y) := sorry

/-- A smooth prorepresentable groupoid is minimal when its actual quotient presentation is minimal. -/
abbrev IsMinimal (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [smooth : IsSmooth G.s G.t] [prorepresentable : IsProrepresentable G] : Prop :=
  FormalObject.IsMinimalPresentation G.forgetULift G.U G.quotientMorphismULift

/-- Minimality supplies an actual prorepresentation with a minimal versal quotient formal object. -/
theorem isMinimal_iff (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    IsMinimal G ↔ ∃ (R : CompleteLocalAlgCat Λ k)
      (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R),
      FormalObject.IsMinimalVersal (G.quotientFormalObject e) :=
  ⟨fun minimal ↦ minimal.exists_minimal_prorepresentation, fun witness ↦ ⟨witness⟩⟩

/-- The discrete groupoid on a restricted coyoneda is normalized. -/
theorem normalized_discrete (R : CompleteLocalAlgCat Λ k) :
    IsNormalized (discrete (CompleteLocalAlgCat.restrictedCoyoneda R))
      (smooth := instIsSmoothId)
      (prorepresentable := instIsProrepresentableFunctorsRestrictedCoyoneda R R) := ⟨rfl⟩

/-- The discrete groupoid on a restricted coyoneda has a minimal quotient presentation. -/
theorem minimal_discrete (R : CompleteLocalAlgCat Λ k) :
    IsMinimal (discrete (CompleteLocalAlgCat.restrictedCoyoneda R))
      (smooth := instIsSmoothId)
      (prorepresentable := instIsProrepresentableFunctorsRestrictedCoyoneda R R) := sorry

end CategoryTheory.GroupoidInFunctors
