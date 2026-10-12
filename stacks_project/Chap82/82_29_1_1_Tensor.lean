/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap82.Remark_82_28_5_ChernClass

/-!
# Tensor-twist formula for Chern classes on algebraic spaces

The binomial identity for `c_i(E ⊗ L)` as an equality of cap operations on all
good tests `Y ⟶ X`, using the operational classes of Remark 82.28.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Invertible `𝒪_X`-modules are finite locally free. -/
instance instIsFiniteLocallyFree_of_isInvertibleObject {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] :
    SheafOfModules.IsFiniteLocallyFree L :=
  sorry

/-- Finite locally free `𝒪_X`-modules are closed under tensor product. -/
instance instIsFiniteLocallyFree_tensor {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E L : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    [SheafOfModules.IsFiniteLocallyFree L] :
    SheafOfModules.IsFiniteLocallyFree (E ⊗ L) :=
  sorry

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable {δ : Points B → ℤ} [IsDimensionFunction δ]
variable {f : X ⟶ B} [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Integer reindex `(k - j) - 1 = k - (j + 1)` for iterated degree-1 caps. -/
theorem powCap_degree_succ (k : ℤ) (j : ℕ) :
    (k - (j : ℤ)) - 1 = k - ((j + 1 : ℕ) : ℤ) :=
  sorry

/-- Zero-fold iteration of a degree-1 cap, reindexing along `k - 0 = k`. -/
def powCapZero : ChowCohomology.CapFamily δ f 0 :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    ChowCohomology.castChowGroup δ (g ≫ f) (sub_zero k).symm

/-- One further composition of a degree-1 cap with a degree-`j` iterated cap. -/
def powCapSucc (c : ChowCohomology.degree δ f 1) (j : ℕ)
    (ih : ChowCohomology.CapFamily δ f j) :
    ChowCohomology.CapFamily δ f (j + 1) :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    (ChowCohomology.castChowGroup δ (g ≫ f)
        ((congrArg (fun n : ℤ ↦ k - n) (Nat.cast_add_one j)).trans
          (sub_add_eq_sub_sub k (j : ℤ) 1)).symm).comp
      ((c.cap g (k - (j : ℤ))).comp (ih g k))

/-- Iterate a degree-1 identity class by composing its cap maps. -/
def powCap (c : ChowCohomology.degree δ f 1) :
    (j : ℕ) → ChowCohomology.CapFamily δ f j :=
  Nat.rec powCapZero (fun j ih ↦ powCapSucc c j ih)

/-- The 0-fold iterated cap is reindexing along `k - 0 = k`. -/
theorem powCap_zero (c : ChowCohomology.degree δ f 1) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    powCap c 0 g k = ChowCohomology.castChowGroup δ (g ≫ f) (sub_zero k).symm :=
  sorry

/-- Recursive unfolding of iterated degree-1 caps. -/
theorem powCap_succ (c : ChowCohomology.degree δ f 1) (j : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    powCap c (j + 1) g k =
      (ChowCohomology.castChowGroup δ (g ≫ f) (powCap_degree_succ k j)).comp
        ((c.cap g (k - (j : ℤ))).comp (powCap c j g k)) :=
  sorry

/-- Reindex `(k - j) - (i - j) = k - i` when `j ≤ i`. -/
theorem powCap_comp_degree (k : ℤ) {i j : ℕ} (h : j ≤ i) :
    (k - (j : ℤ)) - ((i - j : ℕ) : ℤ) = k - (i : ℤ) :=
  sorry

/-- For a good algebraic space `X` over a universally catenary quasi-separated
base `B`, a finite locally free `𝒪_X`-module `E` of rank `r`, and an invertible
`𝒪_X`-module `L`, the identity `c_i(E ⊗ L) = ∑ j, Nat.choose (r + j - i) j •
c_{i-j}(E) * c_1(L)^j` holds as an equality of cap operations on every good
test `g : Y ⟶ X`. -/
theorem chernClass_tensor_invertible {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E L : X.Modules) (r i : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [isInvertibleObject L]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) (α : chowGroup (g ≫ f) δ k) :
    (ChernClass.chernClass δ f (E ⊗ L) i).cap g k α =
      ∑ j ∈ Finset.range (i + 1),
        Nat.choose (r + j - i) j •
          (if hj : j ≤ i then
            ChowCohomology.castChowGroup δ (g ≫ f) (powCap_comp_degree k hj)
              ((ChernClass.chernClass δ f E (i - j)).cap g (k - (j : ℤ))
                (powCap (ChernClass.chernClass δ f L 1) j g k α))
          else 0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
