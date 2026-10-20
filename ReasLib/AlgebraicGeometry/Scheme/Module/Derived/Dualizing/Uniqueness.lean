/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- Any two dualizing complexes on a locally Noetherian scheme differ, up to isomorphism,
by tensoring with an invertible derived module object. -/
theorem existsInvertibleTensorIso
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    {K K' : ModuleDerived X.toRingedSpace}
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    ∃ L : ModuleDerived X.toRingedSpace,
      MonoidalCategory.isInvertibleObject L ∧ Nonempty (K' ≅ K ⊗ L) := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
