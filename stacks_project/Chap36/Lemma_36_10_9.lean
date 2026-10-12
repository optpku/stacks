/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.TensorComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

/- Lemma 36.10.9 (1): the canonical map from the derived tensor product with an internal Hom
to the internal Hom into the derived tensor product is an isomorphism when its source `M` is
perfect. -/
@[stacks 0ATN] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorLeft.comparison_isIso_of_source_isPerfect :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (hM : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect M.obj),
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj))

/- Lemma 36.10.9 (2): the canonical map from the derived tensor product with an internal Hom
to the internal Hom into the derived tensor product is an isomorphism when its tensor factor
`K` is perfect. -/
@[stacks 0ATN] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorLeft.comparison_isIso_of_tensor_isPerfect :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (hK : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect K.obj),
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj))

/- Lemma 36.10.9 (3): the canonical map from the derived tensor product with an internal Hom
to the internal Hom into the derived tensor product is an isomorphism when `M` is
pseudo-coherent, `L` is bounded below, and `K` has finite Tor dimension. -/
@[stacks 0ATN] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorLeft.comparison_isIso_of_pseudoCoherent_boundedBelow_finiteTorDimension :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
    (K L M : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (hM : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent M.obj)
    (hL : (t.plus : ObjectProperty
      (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)) L.obj)
    (hK : AlgebraicGeometry.RingedSpace.HasFiniteTorDimension K.obj),
    IsIso (MonoidalClosed.TensorInternalHom.comparisonOf H K.obj L.obj M.obj))
