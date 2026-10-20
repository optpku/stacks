module

public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology
public import stacks_project.Chap82.Lemma_82_23_4_DoubleZero

/-!
# Commutativity of Gysin maps for two invertible sections

In Situation 82.2.1, the refined Gysin maps of two Definition 82.22.1 triples
commute on Chow groups after the canonical interchange of iterated zero
schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DoubleZero
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.23.4: In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` and `(L', s', i' : D' ⟶ X)` be two triples as in
Definition 82.22.1. Then the square of Gysin maps
`CH_{k+2}(X) ⟶ CH_{k+1}(D)`, `CH_{k+2}(X) ⟶ CH_{k+1}(D')`, and the two
Gysin maps into `CH_k` of the two presentations of `D ∩ D'` commutes, after
identifying `Z(s|_{D'}) ≅ Z(s'|_{D})` by `DoubleZero.swapIso`. This is the
source diagram on `CH_k`, `CH_{k-1}`, `CH_{k-2}` reindexed so that
`Hom.chowGysin` compositions land in degree `k`. -/
@[stacks 0ERC]
theorem chowGysin_comm {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)]
    (k : ℤ) :
    (chowGysin δ (zeroSchemeι L s ≫ f)
        ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s') k).comp
      (chowGysin δ f L s (k + 1)) =
    (properPushforward δ
        ((iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f)
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f)
        (swapIso L L' s s').hom (swapIso_hom_comp_structure f L L' s s')
        k).comp
      ((chowGysin δ (zeroSchemeι L' s' ≫ f)
          ((Modules.pullback (zeroSchemeι L' s')).obj L)
          (Modules.sectionsPullback (zeroSchemeι L' s') L s) k).comp
        (chowGysin δ f L' s' (k + 1))) :=
  sorry

/-- Pointwise form of Gysin commutativity on a class in `CH_{k+2}(X)`. -/
theorem chowGysin_comm_apply {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)]
    (k : ℤ) (α : chowGroup f δ (k + 1 + 1)) :
    chowGysin δ (zeroSchemeι L s ≫ f)
        ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s') k
      (chowGysin δ f L s (k + 1) α) =
    properPushforward δ
        ((iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f)
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f)
        (swapIso L L' s s').hom (swapIso_hom_comp_structure f L L' s s') k
      (chowGysin δ (zeroSchemeι L' s' ≫ f)
        ((Modules.pullback (zeroSchemeι L' s')).obj L)
        (Modules.sectionsPullback (zeroSchemeι L' s') L s) k
        (chowGysin δ f L' s' (k + 1) α)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
