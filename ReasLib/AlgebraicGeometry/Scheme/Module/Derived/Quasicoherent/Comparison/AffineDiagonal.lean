/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.Qcqs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine

/-!
# Comparison for schemes with affine diagonal

The canonical comparison from the derived category of quasicoherent modules on a
quasi-compact scheme with affine diagonal is an equivalence, with the derived coherator
as quasi-inverse. It is compatible with derived pushforward between such schemes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a quasi-compact scheme with affine diagonal, the canonical comparison and the
restricted derived coherator are quasi-inverse. -/
theorem comparison_isQuasiInverse_of_compact_affineDiagonal
    {X : Scheme.{u}} [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    (comparison X).IsQuasiInverse
      ((DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
        (Scheme.Modules.ringedSpaceEquivalence X).mapDerivedCategory.inverse ⋙
        QCoh.Derived.coherator X) := sorry

/-- The canonical comparison from derived quasicoherent modules to ambient derived modules
with quasicoherent cohomology is an equivalence on a quasi-compact scheme with affine diagonal. -/
instance comparisonIsEquivalenceOfCompactAffineDiagonal
    (X : Scheme.{u}) [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    (comparison X).IsEquivalence := sorry

/-- For a morphism between quasi-compact schemes with affine diagonal, derived quasicoherent
pushforward commutes up to natural isomorphism with comparison to ambient derived modules
having quasicoherent cohomology. -/
theorem pushforwardComparison_isomorphic_of_compact_affineDiagonal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforwardCohomologyIn f) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
