module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.ClosedEmbedding
import StacksCheckRecall

/-!
# Lemma 29.45.4

The reusable closed-embedding affineness criterion is owned by
`ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.ClosedEmbedding`.

@stack 04DE
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.45.4: a scheme morphism that is a homeomorphism onto a closed subset is affine. -/
@[stacks 04DE] #check
  (@AlgebraicGeometry.isAffineHom_of_base_isClosedEmbedding :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      Topology.IsClosedEmbedding ⇑(ConcreteCategory.hom f.base) →
        AlgebraicGeometry.IsAffineHom f)
