module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_27_1_QuasiFinite
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap68.Lemma_68_12_8_Decent

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

/-- Lemma 76.33.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
@[stacks 082H]
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

/-- The clopen étale neighbourhood decomposition when `f` is quasi-compact. -/
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
  sorry

/-- The clopen étale neighbourhood decomposition when `Y` is decent. -/
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
  sorry

end AlgebraicGeometry.AlgebraicSpace
