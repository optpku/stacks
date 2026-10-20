/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- The normalization morphism of a locally finite type scheme over an analytically
unramified Noetherian local ring is finite if its structural morphism is étale at every
generic point. -/
@[stacks 0BG8]
theorem isFinite_of_analyticallyUnramified_of_genericEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAnalyticallyUnramified A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (h_etale : ∀ x : X, x ∈ genericPoints X → f.EtaleAt x) :
    -- Local instance justification (search instability): `X` does not determine `f`, which canonically supplies the instance needed by `normalizationTo`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsFinite X.normalizationTo := sorry

end AlgebraicGeometry.Scheme.Normalization
