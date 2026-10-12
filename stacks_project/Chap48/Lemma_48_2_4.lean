/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.TensorComparison

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

/- Lemma 48.2.4 (1): if `K` has bounded-above coherent cohomology, `L` has
bounded-below coherent cohomology, and `M` affine locally has finite injective dimension,
then the canonical map `RHom(L, M) ⊗ᴸ K ⟶ RHom(RHom(K, L), M)` is an isomorphism. -/
@[stacks 0G4I] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorRight.comparison_isIso_of_coherentBounds_finiteInjectiveDimension :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (K L M : Scheme.ModuleDerived.Quasicoherent X),
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K.obj →
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj →
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L.obj →
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj →
        Scheme.DerivedQCoh.AffineLocallyHasFiniteInjectiveDimension M →
        IsIso (MonoidalClosed.TensorRight.comparisonOf H K.obj L.obj M.obj))

/- Lemma 48.2.4 (2): if `K` and `L` have bounded coherent cohomology,
`RHom(L, M)` has finite Tor dimension, and `L` and `M` affine locally have finite injective
dimension, then the canonical map `RHom(L, M) ⊗ᴸ K ⟶ RHom(RHom(K, L), M)` is an
isomorphism. -/
@[stacks 0G4I] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.TensorRight.comparison_isIso_of_boundedCoherent_finiteDimensions :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (K L M : Scheme.ModuleDerived.Quasicoherent X),
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K.obj →
        (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj →
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L.obj →
        (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj →
        RingedSpace.HasFiniteTorDimension ((ihomOf H L.obj).obj M.obj) →
        Scheme.DerivedQCoh.AffineLocallyHasFiniteInjectiveDimension L →
        Scheme.DerivedQCoh.AffineLocallyHasFiniteInjectiveDimension M →
        IsIso (MonoidalClosed.TensorRight.comparisonOf H K.obj L.obj M.obj))
