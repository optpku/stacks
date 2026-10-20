module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineRingedComparison
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite
public import stacks_project.Chap96.Lemma_96_24_3

/-!
# Affine comparison of associated ringed topoi

The canonical ringed-topos comparison is induced by the affine inclusion and
the restriction of the lifted structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.GroupoidsOver.associatedAffineComparison :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology)
    [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
    [∀ P : (GroupoidsOver.Affine X)ᵒᵖ ⥤ Type (u + 1),
      (GroupoidsOver.affineInclusion X).op.HasPointwiseRightKanExtension P]
    [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
    [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})],
    RingedSite.ToposHom (GroupoidsOver.associatedAffineRingedSite X τ)
      (GroupoidsOver.liftedAssociatedRingedSite X τ))
