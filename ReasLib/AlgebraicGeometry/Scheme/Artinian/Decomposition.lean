/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Artinian
public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Coproduct

/-!
# Decomposition of locally Artinian schemes

This file records the Artinian stalks of a locally Artinian scheme and the
canonical decomposition of such a scheme as the coproduct of its stalk
spectra.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Every stalk ring of a locally Artinian scheme is Artinian. -/
instance IsLocallyArtinian.isArtinianRing_stalk
    (X : Scheme.{u}) [IsLocallyArtinian X] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := sorry

/-- For a locally Artinian scheme, the canonical map from the coproduct of its stalk spectra is
an isomorphism. -/
instance IsLocallyArtinian.stalkSpectrumCoproductTo_isIso
    (X : Scheme.{u}) [IsLocallyArtinian X] :
    IsIso (stalkSpectrumCoproductTo X) := sorry

/-- For a locally Noetherian scheme of topological Krull dimension zero, the canonical map from
the coproduct of its stalk spectra is an isomorphism. -/
theorem isIso_stalkSpectrumCoproductTo_of_topologicalKrullDim_eq_zero
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hXdim : topologicalKrullDim X = 0) :
    IsIso (stalkSpectrumCoproductTo X) := by
  -- Local instance justification (proof-local temporary data): hXdim supplies the canonical IsLocallyArtinian instance only within this theorem.
  letI : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hXdim.le
  infer_instance

/-- Every stalk ring of a locally Noetherian scheme of topological Krull dimension zero is
Artinian. -/
theorem isArtinianRing_stalk_of_topologicalKrullDim_eq_zero
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hXdim : topologicalKrullDim X = 0) (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  -- Local instance justification (proof-local temporary data): hXdim supplies the canonical IsLocallyArtinian instance only within this theorem.
  letI : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hXdim.le
  infer_instance

end AlgebraicGeometry
