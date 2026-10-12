/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap82.Remark_82_28_5_ChernClass

/-!
# Vanishing of the top Chern class after removing a trivial subbundle

In Situation 82.2.1, a short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0` of
finite locally free sheaves of ranks `r` and `r - 1` yields equalities of
operational Chern classes in `A^*(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- Lemma 82.30.1 (1): In Situation 82.2.1, let `X / B` be good. Let `E`, `F`
be finite locally free sheaves on `X` of ranks `r`, `r - 1` which fit into a
short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0`. Then `chernClass δ f E r = 0`
in `ChowCohomology.degree δ f r`. -/
@[stacks 0ES7]
theorem top_eq_zero_of_unit_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : 𝟙_ X.Modules ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact) :
    chernClass δ f E r = 0 :=
  sorry

/-- Lemma 82.30.1 (2): In Situation 82.2.1, let `X / B` be good. Let `E`, `F`
be finite locally free sheaves on `X` of ranks `r`, `r - 1` which fit into a
short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0`. Then
`chernClass δ f E j = chernClass δ f F j` for every `j < r`, as classes in
`ChowCohomology.degree δ f j`. -/
@[stacks 0ES7]
theorem component_eq_of_unit_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : 𝟙_ X.Modules ⟶ E) (q : E ⟶ F)
    (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
    (j : ℕ) (hj : j < r) :
    chernClass δ f E j = chernClass δ f F j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
