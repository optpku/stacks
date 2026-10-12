/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_8_Normalization

/-!
# Étale base change of relative normalization

The formation of the relative normalization of a quasi-compact and
quasi-separated morphism of algebraic spaces commutes with étale base change.
The comparison map `W ×_Y X ⟶ W ×_Y X'` is the `pullback.map` induced by
`Hom.toNormalization`, and the pulled-back factorization is a relative
normalization in the sense of `IsNormalization`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The cospan identity `f ≫ 𝟙 Y = Hom.toNormalization f ≫ Hom.fromNormalization f`
used to induce `pullbackToNormalization`. -/
theorem pullbackToNormalization_map_eq₁ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    f ≫ 𝟙 Y = Hom.toNormalization f ≫ Hom.fromNormalization f :=
  sorry

/-- The identity-leg identity `g ≫ 𝟙 Y = 𝟙 W ≫ g` used to induce
`pullbackToNormalization`. -/
theorem pullbackToNormalization_map_eq₂ {S : Scheme.{u}} {Y W : AlgebraicSpace S}
    (g : W ⟶ Y) : g ≫ 𝟙 Y = 𝟙 W ≫ g :=
  sorry

/-- The morphism `W ×_Y X ⟶ W ×_Y Hom.normalization f` induced by
`Hom.toNormalization f`. In Stacks language this is `W ×_X Y ⟶ W ×_X X'`. -/
def pullbackToNormalization {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    (f : X ⟶ Y) (g : W ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback f g] [HasPullback (Hom.fromNormalization f) g] :
    pullback f g ⟶ pullback (Hom.fromNormalization f) g :=
  pullback.map f g (Hom.fromNormalization f) g
    (Hom.toNormalization f) (𝟙 W) (𝟙 Y)
    (pullbackToNormalization_map_eq₁ f) (pullbackToNormalization_map_eq₂ g)

/-- The first projection identity for `pullbackToNormalization`. -/
theorem pullbackToNormalization_fst {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    (f : X ⟶ Y) (g : W ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback f g] [HasPullback (Hom.fromNormalization f) g] :
    pullbackToNormalization f g ≫ pullback.fst (Hom.fromNormalization f) g =
      pullback.fst f g ≫ Hom.toNormalization f :=
  sorry

/-- The second projection identity for `pullbackToNormalization`. -/
theorem pullbackToNormalization_snd {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    (f : X ⟶ Y) (g : W ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback f g] [HasPullback (Hom.fromNormalization f) g] :
    pullbackToNormalization f g ≫ pullback.snd (Hom.fromNormalization f) g =
      pullback.snd f g :=
  sorry

/-- Étale base change preserves relative normalization of algebraic spaces: the
pulled-back factorization of a qcqs morphism along an étale morphism is a
relative normalization. -/
theorem isNormalization_pullback_snd_of_etale {S : Scheme.{u}}
    {X Y W : AlgebraicSpace S} (f : X ⟶ Y) (g : W ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Etale g]
    [HasPullback f g] [HasPullback (Hom.fromNormalization f) g] :
    IsNormalization (pullback.snd f g) (pullbackToNormalization f g)
      (pullback.snd (Hom.fromNormalization f) g) :=
  sorry

/-- Étale base change of relative normalization, in `IsPullback` form: if
`P` and `P'` present `W ×_Y X` and `W ×_Y Hom.normalization f`, then a
comparison `P ⟶ P'` compatible with `Hom.toNormalization f` is a relative
normalization of `W` in `P`. -/
theorem isNormalization_isPullback_of_etale {S : Scheme.{u}}
    {X Y W P P' : AlgebraicSpace S} (f : X ⟶ Y) (g : W ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Etale g]
    {pW : P ⟶ W} {pX : P ⟶ X} {pW' : P' ⟶ W}
    {pN : P' ⟶ Hom.normalization f} {toP' : P ⟶ P'}
    (sq : IsPullback pW pX g f)
    (sq' : IsPullback pW' pN g (Hom.fromNormalization f))
    (hN : toP' ≫ pN = pX ≫ Hom.toNormalization f)
    (hW : toP' ≫ pW' = pW) :
    IsNormalization pW toP' pW' :=
  sorry

/-- The constructed étale pullback of `Hom.normalization f` is the unique
comparison target for `Hom.normalization (pullback.snd f g)`. -/
theorem existsUnique_hom_normalization_etalePullback {S : Scheme.{u}}
    {X Y W : AlgebraicSpace S} (f : X ⟶ Y) (g : W ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Etale g]
    [HasPullback f g] [HasPullback (Hom.fromNormalization f) g]
    [QuasiCompact (pullback.snd f g)] [QuasiSeparated (pullback.snd f g)] :
    ∃! h : Hom.normalization (pullback.snd f g) ⟶
        pullback (Hom.fromNormalization f) g,
      Hom.toNormalization (pullback.snd f g) ≫ h =
          pullbackToNormalization f g ∧
        h ≫ pullback.snd (Hom.fromNormalization f) g =
          Hom.fromNormalization (pullback.snd f g) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace

