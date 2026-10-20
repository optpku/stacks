/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.Affine
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced

/-!
# Normalization and meromorphic functions

For a reduced scheme with finitely many irreducible components on quasi-compact opens, the
normalization is locally the spectrum of the integral closure of regular functions in meromorphic
functions.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.MeromorphicFunction

/-- The spectrum morphism to an affine open induced by the canonical map from regular functions
to their integral closure in the ring of meromorphic sections. -/
noncomputable def integralClosureSpecToAffineOpen (X : Scheme.{u}) (U : X.affineOpens) :
    Spec (CommRingCat.of (integralClosure Γ(X, (U : X.Opens))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op (U : X.Opens))))) ⟶
      (U : X.Opens).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, (U : X.Opens))
    (integralClosure Γ(X, (U : X.Opens))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op (U : X.Opens)))))) ≫
    U.2.isoSpec.inv

/-- For a reduced scheme with finitely many irreducible components on quasi-compact opens, the
normalization restricted to an affine open is isomorphic over that open to the spectrum of the
integral closure of regular functions in meromorphic functions. -/
theorem normalizationTo_restrict_isIsomorphic_integralClosureSpec
    (X : Scheme.{u}) [IsReduced X] [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.affineOpens) :
    IsIsomorphic (Over.mk (X.normalizationTo ∣_ (U : X.Opens)))
      (Over.mk (integralClosureSpecToAffineOpen X U)) := sorry

end AlgebraicGeometry.Scheme.Normalization.MeromorphicFunction
