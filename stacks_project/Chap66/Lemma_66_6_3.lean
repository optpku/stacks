module

public import stacks_project.Chap66.Lemma_66_6_3_AffineCover
import StacksCheckRecall

@[expose] public section

/- Lemma 66.6.3: let `S` be a scheme. Let `X` be an algebraic space over `S`. Then `X` is
quasi-compact if and only if there exists an étale surjective morphism `U ⟶ X` with `U` an
affine scheme. -/
@[stacks 03H6] #check AlgebraicGeometry.AlgebraicSpace.isQuasiCompact_iff_exists_affineEtale
