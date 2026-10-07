module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent

/-!
# Tensor/internal-Hom comparison on algebraic spaces

The Cohomology-on-Sites comparison morphism
`K ⊗ RHom(M, L) ⟶ RHom(M, K ⊗ L)` is an isomorphism for objects of
`D_QCoh(𝒪_X)` when `M` is perfect, when `K` is perfect, or when `M` is
pseudo-coherent, `L` is bounded below, and `K` has finite Tor dimension.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft

/-- The tensor-left comparison morphism is an isomorphism when its internal-Hom source is
perfect. -/
theorem comparison_isIso_of_source_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) (K L M : DerivedQCoh X)
    (hM : ModuleDerived.IsPerfect M.obj) :
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj) := sorry

/-- The tensor-left comparison morphism is an isomorphism when its tensor factor is perfect. -/
theorem comparison_isIso_of_tensor_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) (K L M : DerivedQCoh X)
    (hK : ModuleDerived.IsPerfect K.obj) :
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj) := sorry

/-- The tensor-left comparison morphism is an isomorphism when its internal-Hom source is
pseudo-coherent, its target is bounded below, and its tensor factor has finite Tor dimension. -/
theorem comparison_isIso_of_pseudoCoherent_boundedBelow_finiteTorDimension
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X)) (K L M : DerivedQCoh X)
    (hM : IsPseudoCoherent X M.obj)
    (hL : (t.plus : ObjectProperty (ModuleDerived X)) L.obj)
    (hK : DerivedCategory.DerivedTensor.HasFiniteTorDimension K.obj) :
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft
