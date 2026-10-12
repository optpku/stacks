/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Subobject.Lattice
public import stacks_project.Chap82.Lemma_82_30_2

/-!
# Total Chern class of a filtration by invertible quotients

In Situation 82.2.1, a finite locally free sheaf with an invertible-quotient
flag has total Chern class the ordered product of the factors `1 + c₁(L i)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- Lemma 82.30.4: In Situation 82.2.1 let `X / B` be good. Let `L i`,
`i = 1, …, r` be invertible `𝒪_X`-modules. Let `E` be a locally free
`𝒪_X`-module of rank `r` endowed with a filtration
`0 = E 0 ⊂ ⋯ ⊂ E r = E` such that `E i / E (i - 1) ≅ L i`. Then
`c(E) = ∏_{i = 1}^r (1 + c₁(L i))` in `A^*(X)`. -/
@[stacks 0ESA]
theorem total_eq_prod_of_invertible_filtration
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (L : Fin r → X.Modules) [∀ i : Fin r, isInvertibleObject (L i)]
    (F : Fin (r + 1) → Subobject E)
    (hstep : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hzero : F 0 = ⊥) (htop : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r,
      cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hstep i)) ≅ L i) :
    (∑ i : Fin (r + 1), homogeneous δ f i.val (chernClass δ f E i.val)) =
      (List.ofFn fun i : Fin r ↦
        1 + homogeneous δ f 1 (chernClass δ f (L i) 1)).prod :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
