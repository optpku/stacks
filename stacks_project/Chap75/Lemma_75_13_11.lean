module

public import stacks_project.Chap75.Lemma_75_13_11_TensorComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

/- Lemma 75.13.11 (1): the canonical map from the derived tensor product with an internal Hom
to the internal Hom into the derived tensor product is an isomorphism when its source `M` is
perfect. -/
@[stacks 0E4Q] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft.comparison_isIso_of_source_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X)) (K L M : DerivedQCoh X),
      ModuleDerived.IsPerfect M.obj →
        IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj))

/- Lemma 75.13.11 (2): the canonical map from the derived tensor product with an internal Hom
to the internal Hom into the derived tensor product is an isomorphism when its tensor factor
`K` is perfect. -/
@[stacks 0E4Q] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft.comparison_isIso_of_tensor_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X)) (K L M : DerivedQCoh X),
      ModuleDerived.IsPerfect K.obj →
        IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj))

/- Lemma 75.13.11 (3): the canonical map from the derived tensor product with an internal Hom
to the internal Hom into the derived tensor product is an isomorphism when `M` is
pseudo-coherent, `L` is bounded below, and `K` has finite Tor dimension. -/
@[stacks 0E4Q] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft.comparison_isIso_of_pseudoCoherent_boundedBelow_finiteTorDimension :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X)) (K L M : DerivedQCoh X),
      IsPseudoCoherent X M.obj →
        (t.plus : ObjectProperty (ModuleDerived X)) L.obj →
          DerivedCategory.DerivedTensor.HasFiniteTorDimension K.obj →
            IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj))
