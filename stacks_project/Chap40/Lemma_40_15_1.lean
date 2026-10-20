/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IndQuasiAffine.GlobalSections
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped AlgebraicGeometry

universe u

/- Lemma 40.15.1 (1): if `E` is realized inside an ind-quasi-affine scheme as the
intersection of a nonempty family of quasi-compact opens, then `E.toSpecΓ` is an embedding and
induces isomorphisms on all stalks. -/
@[stacks 0API] #check
  (AlgebraicGeometry.Scheme.IsIndQuasiAffine.toSpecΓ_isLocallyRingedEmbedding :
    ∀ {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X),
      IsEmbedding i →
      [∀ e : E, IsIso (i.stalkMap e)] →
      (∃ S : Set (CompactOpens X),
        S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) →
      IsEmbedding E.toSpecΓ ∧ ∀ e : E, IsIso (E.toSpecΓ.stalkMap e))

/- Lemma 40.15.1 (2): the image of `E.toSpecΓ` is the intersection of a nonempty family of
quasi-compact opens in `Spec Γ(E, ⊤)`. -/
@[stacks 0API] #check
  (AlgebraicGeometry.Scheme.IsIndQuasiAffine.exists_compactOpens_range_toSpecΓ :
    ∀ {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X),
      IsEmbedding i →
      [∀ e : E, IsIso (i.stalkMap e)] →
      (∃ S : Set (CompactOpens X),
        S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) →
      ∃ T : Set (CompactOpens (Spec Γ(E, ⊤))),
        T.Nonempty ∧ Set.range E.toSpecΓ = ⋂ V ∈ T, (V : Set (Spec Γ(E, ⊤))))

/- Lemma 40.15.1 (3): an ambient open subset of `X` contained in `E` has open image under the
canonical morphism `E.toSpecΓ`. -/
@[stacks 0API] #check
  (AlgebraicGeometry.Scheme.IsIndQuasiAffine.isOpen_image_toSpecΓ :
    ∀ {X E : Scheme.{u}} [X.IsIndQuasiAffine] (i : E ⟶ X),
      IsEmbedding i →
      [∀ e : E, IsIso (i.stalkMap e)] →
      (∃ S : Set (CompactOpens X),
        S.Nonempty ∧ Set.range i = ⋂ U ∈ S, (U : Set X)) →
      ∀ (W : X.Opens), (W : Set X) ⊆ Set.range i →
        IsOpen (E.toSpecΓ '' (i ⁻¹' (W : Set X))))
