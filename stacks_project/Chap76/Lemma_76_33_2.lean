/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.EtaleNeighborhood
import StacksCheckRecall

/-!
# Étale localization splitting off one quasi-finite point

After an étale neighbourhood of the image point, a separated locally finite
type morphism of algebraic spaces that is quasi-finite at a single source
point decomposes the pullback into complementary clopen subspaces with finite
restricted morphism and a lift of the given point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.33.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `x ∈ |X|` with image `y ∈ |Y|`. Assume that
`f` is locally of finite type, `f` is separated, and `f` is quasi-finite at
`x`. Then there exists an étale morphism `(U, u) ⟶ (Y, y)` of pointed
algebraic spaces and a decomposition `U ×_Y X = W ⨿ V` into open and closed
subspaces such that `V ⟶ U` is finite and there exists a point `v ∈ |V|`
which maps to `x` in `|X|` and `u` in `|U|`.

The formal fibre product is `pullback f φ ≅ X ×_Y U`. The identification
`W ⨿ V ≅ pullback f φ` is a colimit of the binary cofan of the clopen
immersions, `V ⟶ U` is `iV ≫ pullback.snd f φ`, and `v` maps to `x` and `u`
via `pullback.fst` and `pullback.snd`. -/
@[stacks 0ADU] #check (AlgebraicGeometry.AlgebraicSpace.exists_clopen_decomposition_etaleNeighborhood_at :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Separated f] (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (hqf : FiniteType.QuasiFiniteAt f x),
    ∃ (U : AlgebraicSpace S) (φ : U ⟶ Y) (u : Points U),
      Etale φ ∧ Points.map φ u = y ∧
        ∃ (W V : AlgebraicSpace S) (iW : W ⟶ pullback f φ)
          (iV : V ⟶ pullback f φ) (v : Points V),
          IsOpenImmersion iW ∧ IsClosedImmersion iW ∧
            IsOpenImmersion iV ∧ IsClosedImmersion iV ∧
            Nonempty (IsColimit (BinaryCofan.mk iW iV)) ∧
            IsFinite (iV ≫ pullback.snd f φ) ∧
            Points.map (iV ≫ pullback.fst f φ) v = x ∧
            Points.map (iV ≫ pullback.snd f φ) v = u)

end AlgebraicGeometry.AlgebraicSpace
