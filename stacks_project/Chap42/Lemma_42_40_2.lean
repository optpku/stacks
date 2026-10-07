module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ExactSequence

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-
Lemma 42.40.2: For a short exact sequence `0 ⟶ L ⟶ E ⟶ F ⟶ 0` in which
`L` is invertible and `E`, `F` are finite locally free of ranks `r`, `r - 1`, the
total Chern class of `E` is the product of the total Chern classes of `L` and `F`.
-/
@[stacks 02UH]
#check
  (AlgebraicGeometry.ChernClass.Theory.total_eq_mul_of_invertible_shortExact :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p) (L E F : X.Modules) (r : ℕ)
      [Scheme.Modules.Invertible L]
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      [Scheme.Modules.IsFiniteLocallyFreeOfRank (r - 1) F]
      (ι : L ⟶ E) (q : E ⟶ F) (hzero : ι ≫ q = 0)
      (hshort : (ShortComplex.mk ι q hzero).ShortExact),
      (∑ i : Fin (r + 1),
        AlgebraicGeometry.ChernClass.homogeneous δ p (i : ℕ) (classes.component E i)) =
        (∑ i : Fin 2,
          AlgebraicGeometry.ChernClass.homogeneous δ p (i : ℕ) (classes.component L i)) *
        (∑ i : Fin ((r - 1) + 1),
          AlgebraicGeometry.ChernClass.homogeneous δ p (i : ℕ) (classes.component F i)))

end AlgebraicGeometry.ChernClass.Theory
