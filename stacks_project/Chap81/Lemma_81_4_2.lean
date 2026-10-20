module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Descent
import StacksCheckRecall

/-!
# Lemma 81.4.2

Descent of small étale sheaves along a morphism of algebraic spaces reduces to
the corresponding descent after étale base change to an étale covering of the
target, including pairwise fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/- Lemma 81.4.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `{g i : Yᵢ i ⟶ Y}` be an étale covering of algebraic spaces.
If for each `i` the functor from sheaves on the small étale site of `Yᵢ i` to
descent data for étale sheaves with respect to `{Limits.pullback.snd f (g i)}`
is an equivalence, and for each `i, j` the corresponding functor for
`{Limits.pullback.snd f (Limits.pullback.fst (g i) (g j) ≫ g i)}` is an
equivalence, then the functor from sheaves on the small étale site of `Y` to
descent data for étale sheaves with respect to `{f}` is an equivalence. -/
@[stacks 0GFT] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfBaseChangeOfEtaleCovering :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {ι : Type u} {Yᵢ : ι → AlgebraicSpace S} (g : ∀ i, Yᵢ i ⟶ Y) [∀ i, Etale (g i)]
    (h_cover : (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (h_i : ∀ i, (pseudofunctor.toDescentData
      (fun _ : PUnit ↦ Limits.pullback.snd f (g i))).IsEquivalence)
    (h_ij : ∀ i j, (pseudofunctor.toDescentData
      (fun _ : PUnit ↦ Limits.pullback.snd f
        (Limits.pullback.fst (g i) (g j) ≫ g i))).IsEquivalence),
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence)

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
