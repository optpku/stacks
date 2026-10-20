module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed

/-!
# Tensor/internal-Hom comparison on algebraic spaces

The canonical derived comparison morphism
`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is an isomorphism for objects of
`D_QCoh(𝒪_X)` when `M` is perfect, when `K` is perfect, or when `M` is
pseudo-coherent, `L` is bounded below, and `K` has finite Tor dimension.
An explicit fixed-right derived tensor model identifies the ambient tensor with the
left-derived structure-ring tensor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft

/-- For the structure-ring derived tensor selected by the explicit fixed-right model `T`,
the tensor/internal-Hom comparison is an isomorphism when its internal-Hom source is perfect. -/
theorem comparison_isIso_of_source_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X))
    (K L M : DerivedQCoh X)
    (hM : ModuleDerived.IsPerfect M.obj) :
    IsIso (DerivedCategory.DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf
      H T K.obj L.obj M.obj) := sorry

/-- For the structure-ring derived tensor selected by the explicit fixed-right model `T`,
the tensor/internal-Hom comparison is an isomorphism when its tensor factor is perfect. -/
theorem comparison_isIso_of_tensor_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X))
    (K L M : DerivedQCoh X)
    (hK : ModuleDerived.IsPerfect K.obj) :
    IsIso (DerivedCategory.DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf
      H T K.obj L.obj M.obj) := sorry

/-- For the structure-ring derived tensor selected by the explicit fixed-right model `T`,
the tensor/internal-Hom comparison is an isomorphism when its internal-Hom source is
pseudo-coherent, its target is bounded below, and its tensor factor has finite Tor dimension. -/
theorem comparison_isIso_of_pseudoCoherent_boundedBelow_finiteTorDimension
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X))
    (K L M : DerivedQCoh X)
    (hM : IsPseudoCoherent X M.obj)
    (hL : (t.plus : ObjectProperty (ModuleDerived X)) L.obj)
    (hK : DerivedCategory.DerivedTensor.HasFiniteTorDimension K.obj) :
    IsIso (DerivedCategory.DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf
      H T K.obj L.obj M.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.TensorLeft
