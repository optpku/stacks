/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.AffineDiagonal

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 36.7.6: for a morphism between quasi-compact schemes with affine diagonal,
right-derived quasicoherent pushforward commutes, up to natural isomorphism, with the
canonical comparisons to derived modules having quasicoherent cohomology. -/
@[stacks 0CRX]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardComparison_isomorphic_of_compact_affineDiagonal :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace X] [CompactSpace Y]
      [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.QCoh.Derived.pushforward f ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.comparison Y)
        (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f))
