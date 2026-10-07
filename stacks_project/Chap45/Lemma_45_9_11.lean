module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.MotivicRealization

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open GradedObject.Monoidal

universe u v w y z

/- Lemma 45.9.11: a scheme-valued classical Weil cohomology theory over an arbitrary
field with characteristic-zero coefficients determines a ℚ-linear strong monoidal
realization of Chow motives in graded `F`-modules, compatible with the Koszul symmetry
and recovering untwisted cohomology on every represented smooth projective scheme. -/
@[stacks 0FHL] #check (WeilCohomology.SchemeClassicalTheory.existsMotivicRealization :
  ∀ {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {H : V → Type v} {CH : V → Type y}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
    {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product fst snd
      point H CH Hgrade CHgrade cyclePullback cyclePushforward),
    ∃ (G : ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
        GradedObject ℤ (ModuleCat F))
      (monoidal : G.Monoidal)
      (comparison : ∀ X : V,
        ((fun i : ℤ ↦ ModuleCat.of F (Hgrade X (i, 0))) :
            GradedObject ℤ (ModuleCat F)) ≅ G.obj (T.motive X)),
      G.Linear ℚ ∧
        ∀ X Y,
          (@Functor.Monoidal.μIso _ _ _ _ _ _ G monoidal X Y).hom ≫
              G.map (β_ X Y).hom =
            koszulBraidingHom (G.obj X) (G.obj Y) ≫
              (@Functor.Monoidal.μIso _ _ _ _ _ _ G monoidal Y X).hom)
