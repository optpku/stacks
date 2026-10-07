module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Filtration

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/- Lemma 42.40.4: If a finite locally free module has a filtration from `⊥` to `⊤`
whose successive quotients are the invertible modules `L i`, then its total Chern
class is the product of the factors `1 + c₁(L i)`. -/
@[stacks 02UJ] #check
  (AlgebraicGeometry.ChernClass.Theory.total_eq_prod_of_invertible_filtration :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : Theory δ p) (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFree E]
      (L : Fin r → X.Modules) [∀ i : Fin r, Scheme.Modules.Invertible (L i)]
      (F : Fin (r + 1) → Subobject E)
      (hstep : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
      (hzero : F 0 = ⊥) (htop : F (Fin.last r) = ⊤)
      (e : ∀ i : Fin r,
        cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hstep i)) ≅ L i),
      (∑ i : Fin (r + 1),
        ChernClass.homogeneous δ p (i : ℕ) (classes.component E i)) =
        (List.ofFn fun i : Fin r ↦
          1 + ChernClass.homogeneous δ p 1 (classes.component (L i) 1)).prod)

end AlgebraicGeometry.ChernClass.Theory
