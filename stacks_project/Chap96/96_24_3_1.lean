module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineRingedComparison
import StacksCheckRecall

/-!
# Restriction to associated affine ringed sites

Restriction of the canonical structure sheaf to the associated affine site
extends the affine comparison to an equivalence of ringed topoi.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- 96.24.3.1: restriction of the canonical structure sheaf to the associated
affine site extends the special cocontinuous comparison to an equivalence
of ringed topoi for every standard topology. -/
@[stacks 0H0C] #check
  (AlgebraicGeometry.GroupoidsOver.associatedAffineComparison_isEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology)
      [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
      [∀ P : (GroupoidsOver.Affine X)ᵒᵖ ⥤ Type (u + 1),
        (GroupoidsOver.affineInclusion X).op.HasPointwiseRightKanExtension P]
      [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
      [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})],
      (GroupoidsOver.associatedAffineComparison X τ).IsEquivalence)
