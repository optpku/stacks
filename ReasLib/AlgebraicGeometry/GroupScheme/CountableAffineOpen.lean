module

public import ReasLib.AlgebraicGeometry.GroupScheme.IdentityComponent
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.CountableCover

/-!
# Countable affine opens in group schemes

This file constructs a clopen countable union of affine opens containing the identity of a group
scheme over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Every group scheme over a field contains its identity point in a clopen open subscheme that
is a countable union of affine opens. -/
theorem existsClopenCountableAffineCover {k : Type u} [Field k]
    (G : SchemeOverField k) [GrpObj G] :
    ∃ U : G.left.Opens,
      η[G].left (IsLocalRing.closedPoint k) ∈ (U : Set G.left) ∧ IsClopen (U : Set G.left) ∧
      ∃ V : ℕ → G.left.Opens, (∀ n, IsAffineOpen (V n)) ∧ iSup V = U := by
  let U := IdentityComponent.openSubset G
  have hUmem : η[G].left (IsLocalRing.closedPoint k) ∈ (U : Set G.left) := by
    -- The chosen open subset is the connected component of the identity point itself.
    rw [show U = IdentityComponent.openSubset G by rfl, IdentityComponent.coe_openSubset]
    exact mem_connectedComponent
  have hUclopen : IsClopen (U : Set G.left) := by
    refine ⟨?_, U.2⟩
    -- The identity component is also the range of a closed immersion.
    have hClosedRange : IsClosed (Set.range (identityComponent G).inclusion.left) := by
      simpa using
        (IsClosedImmersion.isClosedEmbedding (identityComponent G).inclusion.left).isClosed_range
    simpa [U, IdentityComponent.coe_openSubset] using
      (range_identityComponent G ▸ hClosedRange)
  have hUcompact : IsCompact (U : Set G.left) := by
    -- The identity component is the image of a compact subgroup scheme.
    have hCompactRange : IsCompact (Set.range (identityComponent G).inclusion.left) := by
      simpa using isCompact_range (f := (identityComponent G).inclusion.left) (by fun_prop)
    simpa [U, IdentityComponent.coe_openSubset] using
      (range_identityComponent G ▸ hCompactRange)
  obtain ⟨s, hsAffine, hsFinite, hsSup⟩ :=
    G.left.isBasis_affineOpens.exists_finite_of_isCompact hUcompact
  obtain ⟨V, hVaffine, hVsup⟩ :=
    Scheme.natAffineFamilyOfFiniteCover s hsFinite hsAffine hsSup.symm
  -- Reindex the finite affine subcover by `ℕ` and package the clopen witness.
  exact ⟨U, hUmem, hUclopen, V, hVaffine, hVsup⟩

end AlgebraicGeometry.GroupScheme
