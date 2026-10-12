/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.AnalyticallyUnramified
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 54.11.5: if a locally finite type scheme over an analytically unramified
Noetherian local ring is étale at every generic point, then `X.normalizationTo` is finite. -/
@[stacks 0BG8] #check
  (AlgebraicGeometry.Scheme.Normalization.isFinite_of_analyticallyUnramified_of_genericEtale :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsAnalyticallyUnramified A] {X : Scheme.{u}}
      (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
      (h_etale : ∀ x : X, x ∈ genericPoints X → f.EtaleAt x),
    -- Local instance justification (search instability): `X` does not determine `f`, which canonically supplies the instance needed by `normalizationTo`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsFinite X.normalizationTo)
