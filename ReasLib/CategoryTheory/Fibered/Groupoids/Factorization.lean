module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Factorization
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Graph
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of groupoid-fibration factorizations

This module supplies the fixed-target comparison API for factorizations through functors fibred
in groupoids. Morphisms in `Cat/Y` are represented as based functors between
`BasedCategory.ofFunctor` objects; their underlying morphisms in `Cat/C` are obtained by a
separate forgetful bridge.
-/

@[expose] public section

universe u v uX uX' uX'' uY

namespace CategoryTheory

namespace BasedCategory.FactorizationOverTarget

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {X' : BasedCategory.{v, uX'} C}
variable {X'' : BasedCategory.{v, uX''} C}
variable {Y : BasedCategory.{v, uY} C}
variable {F : X ⥤ᵇ Y} {a : X ⥤ᵇ X'} {b : X ⥤ᵇ X''}
variable {f : X' ⥤ᵇ Y} {g : X'' ⥤ᵇ Y}

/-- Two `2`-commutative factorizations through functors fibred in groupoids, whose source maps
admit heterogeneous based quasi-inverses over `C`, have a comparison over `Y` which also admits
a heterogeneous based quasi-inverse. After forgetting to `C`, the comparison composed with the
second source map is `2`-isomorphic to the first. -/
theorem existsComparison
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids f.toFunctor]
    [Functor.IsFibered.InGroupoids g.toFunctor]
    (ha_equiv : a.IsEquivalence)
    (hb_equiv : b.IsEquivalence)
    (ha_comm : Nonempty (BasedFunctor.comp a f ≅ F))
    (hb_comm : Nonempty (BasedFunctor.comp b g ≅ F)) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalence ∧
        Nonempty (BasedFunctor.comp b (BasedFunctor.forgetTarget h) ≅ a) := sorry
/- Proof strategy: compare both factorizations with the identity pseudo-pullback factorization.
The comparison functors are equivalences because this can be checked fiberwise; compose one with
a quasi-inverse of the other and paste the source comparison isomorphisms. -/

/-- If both factorization triangles commute strictly, the comparison can be chosen so that its
composite with the second source map is `2`-isomorphic to the first already in `Cat/Y`. This is
the heterogeneous-universe boundary form of the fixed-owner theorem below. -/
theorem existsStrictComparison
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids f.toFunctor]
    [Functor.IsFibered.InGroupoids g.toFunctor]
    (ha_equiv : a.IsEquivalence)
    (hb_equiv : b.IsEquivalence)
    (ha_strict : BasedFunctor.comp a f = F)
    (hb_strict : BasedFunctor.comp b g = F) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalence ∧
        Nonempty
          (BasedFunctor.comp (BasedFunctor.Factorization.overTarget b hb_strict) h ≅
            BasedFunctor.Factorization.overTarget a ha_strict) := sorry
/- Proof strategy: apply `existsComparison` to the identity triangle
isomorphisms. Strict commutativity makes the resulting comparison vertical over `Y`. -/

/-- A strict comparison can be read simultaneously in `Cat/Y` and, after forgetting the target,
in `Cat/C`. This bundled elimination form avoids reconstructing the weaker comparison in every
heterogeneous-universe consumer. -/
theorem existsCompatibleStrictComparison
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    [Functor.IsFibered.InGroupoids f.toFunctor]
    [Functor.IsFibered.InGroupoids g.toFunctor]
    (ha_equiv : a.IsEquivalence)
    (hb_equiv : b.IsEquivalence)
    (ha_strict : BasedFunctor.comp a f = F)
    (hb_strict : BasedFunctor.comp b g = F) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalence ∧
        Nonempty (BasedFunctor.comp b (BasedFunctor.forgetTarget h) ≅ a) ∧
          Nonempty
            (BasedFunctor.comp (BasedFunctor.Factorization.overTarget b hb_strict) h ≅
              BasedFunctor.Factorization.overTarget a ha_strict) := sorry
/- Proof strategy: unpack `existsStrictComparison`, retain its comparison over
`Y`, and forget that comparison along `Y.p` to obtain the displayed comparison over `C`. -/

end BasedCategory.FactorizationOverTarget

namespace FiberedCategoryOver.Groupoids.Factorization

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X X' X'' Y :
  FiberedCategoryOver.Groupoids.{u, v, max uX (max u v), v} C}
variable {F : X ⟶ Y} {f : X' ⟶ Y} {g : X'' ⟶ Y}

/-- Lemma 4.35.16 (Stacks 06N7): every morphism of categories fibred in groupoids factors
strictly as a bicategorical equivalence followed by a functor fibred in groupoids over its
target.

A proof may use the identity-leg two-fibre-product apex `TwoFibreProduct.apex F (𝟙 Y)`, its graph
equivalence `TwoFibreProduct.graph.equivalence F`, and its second projection
`TwoFibreProduct.snd F (𝟙 Y)`. This theorem deliberately makes no choice of such witnesses:
the existential statement is the source-faithful public surface, while those declarations remain
the data owners. -/
@[stacks 06N7]
theorem existsEquivalence
    (F : X ⟶ Y) :
    ∃ (X' : FiberedCategoryOver.Groupoids.{u, v, max uX (max u v), v} C)
      (e : X ≌ X') (f : X' ⟶ Y),
      e.hom ≫ f = F ∧ Functor.IsFibered.InGroupoids (toFunctor f) := sorry
/- Proof strategy: take the three canonical identity-leg pseudo-pullback witnesses described
above. `TwoFibreProduct.graph.snd F` gives strict commutativity, while the raw
`BasedCategory.PseudoPullback.Snd.inGroupoids` instance gives the target-leg property. -/

/-- Lemma 4.35.17 (Stacks 06N8) (1): two `2`-commutative factorizations through categories
fibred in groupoids, whose source maps
are supplied as bicategorical equivalences, have bicategorically equivalent intermediate
categories over the common target. The second clause records the induced comparison after
forgetting from `Cat/Y` to `Cat/C`. The explicit assumptions on `toFunctor f` and `toFunctor g`
say that both target legs are fibred in groupoids over `Y`. -/
@[stacks 06N8 "(1) equivalence comparison of groupoid-fibration factorizations"]
theorem existsComparison
    [Functor.IsFibered.InGroupoids (toFunctor f)]
    [Functor.IsFibered.InGroupoids (toFunctor g)]
    (a : X ≌ X') (b : X ≌ X'')
    (ha_comm : Nonempty (a.hom ≫ f ≅ F))
    (hb_comm : Nonempty (b.hom ≫ g ≅ F)) :
    ∃ e :
        BasedCategory.ofFunctor (toFunctor g) ≌
          BasedCategory.ofFunctor (toFunctor f),
      Nonempty
        (BasedFunctor.comp (toBasedFunctor b.hom)
            (BasedFunctor.forgetTarget e.hom) ≅
          toBasedFunctor a.hom) := sorry
/- Proof strategy: apply the heterogeneous factorization comparison to the underlying based
functors, then upgrade its same-universe comparison over `Y.total` with
`BasedFunctor.isEquivalence_iff_exists_equivalence`. -/

/-- Lemma 4.35.17 (Stacks 06N8) (2): with strictly commuting factorization triangles, the
comparison equivalence can be chosen so
that its forward morphism commutes with the target maps up to a based natural isomorphism in
`Cat/Y`; both target legs are assumed fibred in groupoids over `Y`. -/
@[stacks 06N8 "(2) strict comparison of groupoid-fibration factorizations"]
theorem existsStrictComparison
    [Functor.IsFibered.InGroupoids (toFunctor f)]
    [Functor.IsFibered.InGroupoids (toFunctor g)]
    (a : X ≌ X') (b : X ≌ X'')
    (ha_strict : a.hom ≫ f = F)
    (hb_strict : b.hom ≫ g = F) :
    ∃ e :
        BasedCategory.ofFunctor (toFunctor g) ≌
          BasedCategory.ofFunctor (toFunctor f),
      Nonempty
        (BasedFunctor.comp
            (BasedFunctor.Factorization.overTarget
              (toBasedFunctor b.hom)
              (congrArg toBasedFunctor hb_strict))
            e.hom ≅
          BasedFunctor.Factorization.overTarget
            (toBasedFunctor a.hom)
            (congrArg toBasedFunctor ha_strict)) := sorry
/- Proof strategy: specialize `existsComparison` to the identity triangle
isomorphisms and retain the resulting forward morphism in `Cat/Y`. -/

end FiberedCategoryOver.Groupoids.Factorization

end CategoryTheory
