module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InjectiveDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorDimension.Affine

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorLeft

/-- The tensor-left comparison morphism is an isomorphism when its internal-Hom source is
perfect. -/
theorem comparison_isIso_of_source_isPerfect {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : ModuleDerived.Quasicoherent X)
    (hM : RingedSpace.ModuleDerived.IsPerfect M.obj) :
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj) := sorry

/-- The tensor-left comparison morphism is an isomorphism when its tensor factor is perfect. -/
theorem comparison_isIso_of_tensor_isPerfect {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : ModuleDerived.Quasicoherent X)
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj) :
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj) := sorry

/-- The tensor-left comparison morphism is an isomorphism when its internal-Hom source is
pseudo-coherent, its target is bounded below, and its tensor factor has finite Tor dimension. -/
theorem comparison_isIso_of_pseudoCoherent_boundedBelow_finiteTorDimension
    {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : ModuleDerived.Quasicoherent X)
    (hM : RingedSpace.ModuleDerived.IsPseudoCoherent M.obj)
    (hL : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj)
    (hK : RingedSpace.HasFiniteTorDimension K.obj) :
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorLeft

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorRight

/-- On a Noetherian scheme, the tensor-right comparison morphism is an isomorphism when its
tensor factor has bounded-above coherent cohomology, its internal-Hom source has bounded-below
coherent cohomology, and its target has affine-locally finite injective dimension. -/
theorem comparison_isIso_of_coherentBounds_finiteInjectiveDimension
    {X : Scheme.{u}} [IsNoetherian X]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : ModuleDerived.Quasicoherent X)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K.obj)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L.obj)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj)
    (hM_injective : DerivedQCoh.AffineLocallyHasFiniteInjectiveDimension M) :
    IsIso (MonoidalClosed.TensorRight.comparisonOf H K.obj L.obj M.obj) := sorry

/-- On a Noetherian scheme, the tensor-right comparison morphism is an isomorphism when its
tensor factor and internal-Hom source have bounded coherent cohomology, the internal Hom into
its target has finite Tor dimension, and the latter two objects have affine-locally finite
injective dimension. -/
theorem comparison_isIso_of_boundedCoherent_finiteDimensions
    {X : Scheme.{u}} [IsNoetherian X]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : ModuleDerived.Quasicoherent X)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K.obj)
    (hK_bounded :
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L.obj)
    (hL_bounded :
      (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj)
    (hLM_tor : RingedSpace.HasFiniteTorDimension ((ihomOf H L.obj).obj M.obj))
    (hL_injective : DerivedQCoh.AffineLocallyHasFiniteInjectiveDimension L)
    (hM_injective : DerivedQCoh.AffineLocallyHasFiniteInjectiveDimension M) :
    IsIso (MonoidalClosed.TensorRight.comparisonOf H K.obj L.obj M.obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorRight
