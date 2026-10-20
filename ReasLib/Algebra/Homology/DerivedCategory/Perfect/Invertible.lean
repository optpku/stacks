/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ExactPairing
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.TruncationSplitting
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.RingTheory.Finiteness.Projective
public import ReasLib.RingTheory.PicardGroup.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible objects in derived categories of modules

This leaf owns the localization criterion for invertibility, its perfectness consequence, and the
resulting cohomological and ring-product decompositions.  The ambient tensor model and tensor-unit
comparison are explicit, so categorical invertibility is tied to the canonical derived tensor
product used by localization.

@stack 0FNT
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped DerivedTensorWithAlgebra

universe u

namespace DerivedCategory

variable {R : Type u} [CommRing R]
variable [MonoidalCategory (DerivedCategory (ModuleCat R))]
variable [BraidedCategory (DerivedCategory (ModuleCat R))]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DModAway[" f "]" => DerivedCategory (ModuleCat (Localization.Away f))
local notation "ringSingleAway[" f "]" =>
  (ModuleCat.single0 (ModuleCat.of (Localization.Away f) (Localization.Away f)) : DModAway[f])
local notation "TensorModel" =>
  CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R)

/-- Lemma 15.127.4, equivalence: a derived object is invertible exactly when it is locally a
shift of the localized tensor unit near every prime. -/
@[stacks 0FNT "equivalence, local criterion for an invertible derived object"]
theorem isInvertibleObject_iff_localizationAway_iso_shift
    (T : TensorModel)
    (s : ((ModuleCat.single0 (ModuleCat.of R R)) : DMod) ≅ 𝟙_ DMod)
    (M : DMod) :
    MonoidalCategory.isInvertibleObject M ↔
      ∀ p : PrimeSpectrum R,
        ∃ f : R, f ∉ p.asIdeal ∧ ∃ n : ℤ,
          IsIsomorphic (M ⊗[R]^L[Localization.Away f]) (ringSingleAway[f]⟦-n⟧) := sorry
-- Proof strategy: derived base change preserves tensor inverses, and an invertible perfect object
-- over a local ring has one rank-one cohomology module in a single degree.  Spread this local
-- description to a principal open neighborhood; conversely glue the local tensor inverses and
-- use Zariski-local detection of isomorphisms for the evaluation map.

/-- Lemma 15.127.4 (a): an invertible object in the derived category of modules is perfect. -/
@[stacks 0FNT "(a) invertible derived objects are perfect"]
theorem IsPerfect.of_isInvertibleObject
    (T : TensorModel)
    (s : ((ModuleCat.single0 (ModuleCat.of R R)) : DMod) ≅ 𝟙_ DMod)
    {M : DMod} (hM : MonoidalCategory.isInvertibleObject M) :
    M.IsPerfect := sorry
-- Proof strategy: choose a tensor inverse of `M`, turn the two inverse isomorphisms into an
-- `ExactPairing`, and apply `CategoryTheory.DerivedCategory.IsPerfect.of_exactPairing` with the
-- explicit tensor-unit comparison `s`.

namespace Invertible

/-- Lemma 15.127.4 (b): an invertible derived object is the finite direct sum of its shifted
cohomology modules. -/
@[stacks 0FNT "(b) decomposition into shifted cohomology"]
theorem existsShiftedCohomologyDecomposition
    (T : TensorModel)
    (s : ((ModuleCat.single0 (ModuleCat.of R R)) : DMod) ≅ 𝟙_ DMod)
    {M : DMod} (hM : MonoidalCategory.isInvertibleObject M) :
    ∃ a b : ℤ, a ≤ b ∧
      Nonempty (M ≅ ⨁ ShiftedCohomology.on (ModuleCat R) M a b) := sorry
-- Proof strategy: first obtain perfectness and bounded cohomological amplitude.  The local
-- invertibility criterion makes the supports of distinct cohomology degrees disjoint, so the
-- relevant truncation triangles split; iterate the splitting across the finite amplitude.

/-- Lemma 15.127.4 (c): every cohomology module of an invertible derived object is finite
projective. -/
@[stacks 0FNT "(c) finite-projective cohomology"]
theorem homologyFiniteProjective
    (T : TensorModel)
    (s : ((ModuleCat.single0 (ModuleCat.of R R)) : DMod) ≅ 𝟙_ DMod)
    {M : DMod} (hM : MonoidalCategory.isInvertibleObject M) (n : ℤ) :
    Module.FiniteProjective R ((homologyFunctor (ModuleCat R) n).obj M) := sorry
-- Proof strategy: perfectness gives finite presentation of each cohomology module, while the
-- local shift criterion makes every localization either zero or free of rank one.  Apply the
-- local criterion for finite projectivity to these localized modules.

/-- Lemma 15.127.4 (d): the base ring decomposes into finitely many factors indexed by the
nonzero cohomological degrees, and each cohomology module is the restriction of an invertible
module over its corresponding factor. -/
@[stacks 0FNT "(d) product decomposition by cohomological degree"]
theorem existsRingProductDecomposition
    (T : TensorModel)
    (s : ((ModuleCat.single0 (ModuleCat.of R R)) : DMod) ≅ 𝟙_ DMod)
    {M : DMod} (hM : MonoidalCategory.isInvertibleObject M) :
    ∃ (a b : ℤ) (hab : a ≤ b)
        (Rpart : Finset.Icc a b → CommRingCat.{u})
        (e : R ≃+* ∀ n, Rpart n)
        (Hpart : ∀ n, ModuleCat.{u} (Rpart n)),
      (∀ n : Finset.Icc a b, Module.Invertible (Rpart n) (Hpart n)) ∧
      (∀ n : Finset.Icc a b, Nonempty
        (((homologyFunctor (ModuleCat R) (n : ℤ)).obj M) ≅
          (ModuleCat.restrictScalars
            ((Pi.evalRingHom (fun i ↦ Rpart i) n).comp e.toRingHom)).obj (Hpart n))) ∧
      ∀ n : ℤ, n < a ∨ b < n →
        IsZero ((homologyFunctor (ModuleCat R) n).obj M) := sorry
-- Proof strategy: use the finite amplitude and the clopen, pairwise-disjoint supports of the
-- finite-projective cohomology modules to obtain orthogonal idempotents and the product
-- decomposition of `R`.  Restrict each cohomology module to its factor, where the local
-- rank-one criterion makes it invertible, and use boundedness outside `[a, b]`.

end Invertible

end DerivedCategory
