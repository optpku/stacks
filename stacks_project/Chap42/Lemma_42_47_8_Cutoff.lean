/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.MixedProduct
public import ReasLib.AlgebraicGeometry.LocalizedChern.Cutoff

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cutoff

#check (AlgebraicGeometry.BivariantClass.Cutoff.mulTerm :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n) (i j : ℕ) (hij : i + j = n)
    (c : Cutoff δ f p (i : ℤ)) (d : Cutoff δ f q (j : ℤ)),
    BivariantClass δ f (n : ℤ))

#check (AlgebraicGeometry.BivariantClass.Cutoff.mulTerm_of_fst_lt :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n) (i j : ℕ) (hij : i + j = n)
    (c : Cutoff δ f p (i : ℤ)) (d : Cutoff δ f q (j : ℤ))
    (hi : (i : ℤ) < p) (hj : ¬(j : ℤ) < q),
    mulTerm δ f p q n hn i j hij c d =
      Nonnegative.castGrading δ
        ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
        (ambientMulRelative δ f i j (toAmbient δ f hi c) (toRelative δ f hj d)))

#check (AlgebraicGeometry.BivariantClass.Cutoff.mixedMul :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n)
    (c : (i : ℕ) → Cutoff δ f p (i : ℤ))
    (d : (j : ℕ) → Cutoff δ f q (j : ℤ)),
    BivariantClass δ f (n : ℤ))

#check (AlgebraicGeometry.BivariantClass.Cutoff.mixedMul_apply :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n)
    (c : (i : ℕ) → Cutoff δ f p (i : ℤ))
    (d : (j : ℕ) → Cutoff δ f q (j : ℤ)),
    mixedMul δ f p q n hn c d =
      @Finset.sum _ (BivariantClass δ f (n : ℤ))
        (pointwiseAddCommGroup δ f (n : ℤ)).toAddCommMonoid
        (Finset.antidiagonal n).attach
        (fun ij ↦ mulTerm δ f p q n hn ij.1.1 ij.1.2
          (Finset.mem_antidiagonal.mp ij.2) (c ij.1.1) (d ij.1.2)))

#check (AlgebraicGeometry.BivariantClass.Cutoff.mixedMul_eq_familyMul :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n)
    (c : Family δ f p) (d : Family δ f q),
    mixedMul δ f p q n hn c d =
      toRelative δ f (not_lt.mpr (Nat.cast_le.mpr hn))
        (familyMul δ f p q c d n))

end AlgebraicGeometry.BivariantClass.Cutoff

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass BivariantClass.Cutoff

#check (AlgebraicGeometry.LocalizedChern.cutoffChernClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ)),
    Cutoff δ i p (n : ℤ))

#check (AlgebraicGeometry.LocalizedChern.cutoffChernClass_apply_lt :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ))
    (h : (n : ℤ) < p),
    toAmbient δ i h (cutoffChernClass δ i p n ambient localized) = ambient)

#check (AlgebraicGeometry.LocalizedChern.cutoffChernClass_apply_ge :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ))
    (h : ¬(n : ℤ) < p),
    toRelative δ i h (cutoffChernClass δ i p n ambient localized) = localized)

end AlgebraicGeometry.LocalizedChern

