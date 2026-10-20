module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.BaseChange
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open AlgebraicGeometry CategoryTheory

/- Lemma 45.10.9: finite separable base change identifies the relative tensor product of
the cohomology of a smooth projective `k'`-scheme with the cohomology of its pullback to `k''`. -/
@[stacks 0FHX] #check (WeilCohomology.SchemeClassicalTheory.cohomologyBaseChange_bijective_of_finiteSeparable :
    ∀ {k k' k'' : Type u} [Field k] [CommRing k'] [CommRing k'']
      [Algebra k k'] [Algebra k' k''] [Algebra k k''] [IsScalarTower k k' k'']
      [Module.Finite k k'] [Algebra.IsSeparable k k']
      [Module.Finite k' k''] [Algebra.IsSeparable k' k'']
      {F : Type v} [Field F] [CharZero F]
      {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V]
      {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {H : V → Type x} {CH : V → Type y}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
      {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
      [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {S' S'' X X'' : V} (s : X ⟶ S') (g : S'' ⟶ S')
      (p : X'' ⟶ X) (q : X'' ⟶ S'')
      (e' : T.scheme.obj S' ≅ Over.mk (Scheme.AffineBaseChange.specMap k k'))
      (e'' : T.scheme.obj S'' ≅ Over.mk (Scheme.AffineBaseChange.specMap k k''))
      (h_g : T.scheme.map g = e''.hom ≫
        Scheme.AffineBaseChange.specMapOverBase k k' k'' ≫ e'.inv)
      [Smooth (T.scheme.map s ≫ e'.hom).left]
      [Projective (T.scheme.map s ≫ e'.hom).left]
      (h_square : IsPullback (T.scheme.map p).left (T.scheme.map q).left
        (T.scheme.map s).left (T.scheme.map g).left),
      Function.Bijective (T.baseChangeComparison s g p q h_square))

end WeilCohomology.SchemeClassicalTheory
