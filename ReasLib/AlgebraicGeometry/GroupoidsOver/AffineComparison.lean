module

public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineTopology

/-!
# Affine comparison for categories fibred in groupoids

The inclusion of affine objects is special cocontinuous for each standard
inherited topology and induces an equivalence on sheaves of types.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- For a category fibred in groupoids over `(Sch/S)_fppf`, the inclusion of
affine objects is special cocontinuous for the inherited Zariski, étale,
smooth, syntomic, or fppf topology. -/
@[stacks 0H0B]
instance affineInclusion_isSpecialCocontinuous (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (affineInclusion X).IsSpecialCocontinuous
      (X.associatedAffineTopology τ) (X.associatedTopology τ) :=
  sorry

/-- The cocontinuous direct image along the affine inclusion is an equivalence
between sheaves of types on the inherited affine and total sites, provided
the pointwise right Kan extensions exist. -/
@[stacks 0H0B]
noncomputable instance affineInclusion_directImage_isEquivalence
    (X : GroupoidsOver S) (τ : StandardTopology)
    [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
      (affineInclusion X).op.HasPointwiseRightKanExtension P] :
    ((affineInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (X.associatedAffineTopology τ) (X.associatedTopology τ)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
    (affineInclusion X)

end AlgebraicGeometry.GroupoidsOver
