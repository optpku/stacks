/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Étale localization splitting off a quasi-finite part

After an étale neighbourhood of a point of the target, a separated locally
finite type morphism of algebraic spaces that is quasi-finite at finitely many
source points, and is quasi-compact or has decent target, decomposes the
pullback into complementary clopen subspaces with finite restricted morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `y ∈ |Y|` and `x : Fin n → Points X` with
`Points.map f (x i) = y`. Assume that `f` is locally of finite type, `f` is
separated, `f` is quasi-finite at each `x i`, and `f` is quasi-compact or `Y`
is decent. Then there exists an étale morphism `(U, u) ⟶ (Y, y)` of pointed
algebraic spaces and a decomposition `U ×_Y X = W ⨿ V` into open and closed
subspaces such that `V ⟶ U` is finite, every point of the fibre of `|V| ⟶ |U|`
over `u` maps to some `x i`, and the fibre of `|W| ⟶ |U|` over `u` contains no
point mapping to any `x i`.

The formal fibre product is `pullback f φ ≅ X ×_Y U`. The identification
`W ⨿ V ≅ pullback f φ` is a colimit of the binary cofan of the clopen
immersions, and `V ⟶ U` is `iV ≫ pullback.snd f φ`. -/
theorem exists_clopen_decomposition_etaleNeighborhood
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Separated f] (y : Points Y) (n : ℕ)
    (x : Fin n → Points X) (hx : ∀ i, Points.map f (x i) = y)
    (hqf : ∀ i, FiniteType.QuasiFiniteAt f (x i))
    (hqc_or_decent : QuasiCompact f ∨ IsDecent Y) :
    ∃ (U : AlgebraicSpace S) (φ : U ⟶ Y) (u : Points U),
      Etale φ ∧ Points.map φ u = y ∧
        ∃ (W V : AlgebraicSpace S) (iW : W ⟶ pullback f φ)
          (iV : V ⟶ pullback f φ),
          IsOpenImmersion iW ∧ IsClosedImmersion iW ∧
            IsOpenImmersion iV ∧ IsClosedImmersion iV ∧
            Nonempty (IsColimit (BinaryCofan.mk iW iV)) ∧
            IsFinite (iV ≫ pullback.snd f φ) ∧
            (∀ v : Points V,
              Points.map (iV ≫ pullback.snd f φ) v = u →
                ∃ i, Points.map (iV ≫ pullback.fst f φ) v = x i) ∧
            ∀ w : Points W,
              Points.map (iW ≫ pullback.snd f φ) w = u →
                ∀ i, Points.map (iW ≫ pullback.fst f φ) w ≠ x i :=
  sorry

/-- A quasi-compact separated locally finite type morphism admits an étale neighbourhood
whose pullback splits into a finite clopen part containing exactly the selected fibre points
and a complementary clopen part avoiding them. -/
theorem exists_clopen_decomposition_etaleNeighborhood_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Separated f] [QuasiCompact f]
    (y : Points Y) (n : ℕ) (x : Fin n → Points X)
    (hx : ∀ i, Points.map f (x i) = y)
    (hqf : ∀ i, FiniteType.QuasiFiniteAt f (x i)) :
    ∃ (U : AlgebraicSpace S) (φ : U ⟶ Y) (u : Points U),
      Etale φ ∧ Points.map φ u = y ∧
        ∃ (W V : AlgebraicSpace S) (iW : W ⟶ pullback f φ)
          (iV : V ⟶ pullback f φ),
          IsOpenImmersion iW ∧ IsClosedImmersion iW ∧
            IsOpenImmersion iV ∧ IsClosedImmersion iV ∧
            Nonempty (IsColimit (BinaryCofan.mk iW iV)) ∧
            IsFinite (iV ≫ pullback.snd f φ) ∧
            (∀ v : Points V,
              Points.map (iV ≫ pullback.snd f φ) v = u →
                ∃ i, Points.map (iV ≫ pullback.fst f φ) v = x i) ∧
            ∀ w : Points W,
              Points.map (iW ≫ pullback.snd f φ) w = u →
                ∀ i, Points.map (iW ≫ pullback.fst f φ) w ≠ x i :=
  exists_clopen_decomposition_etaleNeighborhood f y n x hx hqf (Or.inl inferInstance)

/-- A separated locally finite type morphism to a decent algebraic space admits an étale
neighbourhood whose pullback splits into a finite clopen part containing exactly the selected
fibre points and a complementary clopen part avoiding them. -/
theorem exists_clopen_decomposition_etaleNeighborhood_of_isDecent
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Separated f] [IsDecent Y]
    (y : Points Y) (n : ℕ) (x : Fin n → Points X)
    (hx : ∀ i, Points.map f (x i) = y)
    (hqf : ∀ i, FiniteType.QuasiFiniteAt f (x i)) :
    ∃ (U : AlgebraicSpace S) (φ : U ⟶ Y) (u : Points U),
      Etale φ ∧ Points.map φ u = y ∧
        ∃ (W V : AlgebraicSpace S) (iW : W ⟶ pullback f φ)
          (iV : V ⟶ pullback f φ),
          IsOpenImmersion iW ∧ IsClosedImmersion iW ∧
            IsOpenImmersion iV ∧ IsClosedImmersion iV ∧
            Nonempty (IsColimit (BinaryCofan.mk iW iV)) ∧
            IsFinite (iV ≫ pullback.snd f φ) ∧
            (∀ v : Points V,
              Points.map (iV ≫ pullback.snd f φ) v = u →
                ∃ i, Points.map (iV ≫ pullback.fst f φ) v = x i) ∧
            ∀ w : Points W,
              Points.map (iW ≫ pullback.snd f φ) w = u →
                ∀ i, Points.map (iW ≫ pullback.fst f φ) w ≠ x i :=
  exists_clopen_decomposition_etaleNeighborhood f y n x hx hqf (Or.inr inferInstance)

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
@[stacks 0ADU]
theorem exists_clopen_decomposition_etaleNeighborhood_at
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Separated f] (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (hqf : FiniteType.QuasiFiniteAt f x) :
    ∃ (U : AlgebraicSpace S) (φ : U ⟶ Y) (u : Points U),
      Etale φ ∧ Points.map φ u = y ∧
        ∃ (W V : AlgebraicSpace S) (iW : W ⟶ pullback f φ)
          (iV : V ⟶ pullback f φ) (v : Points V),
          IsOpenImmersion iW ∧ IsClosedImmersion iW ∧
            IsOpenImmersion iV ∧ IsClosedImmersion iV ∧
            Nonempty (IsColimit (BinaryCofan.mk iW iV)) ∧
            IsFinite (iV ≫ pullback.snd f φ) ∧
            Points.map (iV ≫ pullback.fst f φ) v = x ∧
            Points.map (iV ≫ pullback.snd f φ) v = u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
