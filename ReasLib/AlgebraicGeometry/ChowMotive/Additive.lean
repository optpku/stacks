/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.ChowMotive.Twist
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.ProjectiveLine
public import ReasLib.AlgebraicGeometry.Correspondence.Graph.Flat
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace ChowMotive

variable {k : Type u} [Field k]

/-- The zero motive, represented by the empty scheme and the zero projector. -/
def zeroMotive (k : Type u) [Field k] :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  X := (⟨⊥_ (SchemeOverField k), (by sorry : Smooth (⊥_ (SchemeOverField k)).hom ∧
    Projective (⊥_ (SchemeOverField k)).hom)⟩, 0)
  p := 0
  idem := by simp

/-- Every morphism to or from the zero motive is zero. -/
theorem zeroMotive_isZero (k : Type u) [Field k] : IsZero (zeroMotive k) := by
  apply (IsZero.iff_id_eq_zero _).2
  rfl

/-- The empty-scheme motive supplies a zero object. -/
instance instHasZeroObject (k : Type u) [Field k] :
    HasZeroObject (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  (zeroMotive_isZero k).hasZeroObject

/-- The disjoint union of two smooth projective schemes, placed at the first Tate index. -/
def sumAmbient (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    Correspondence.GradedCategory k :=
  (⟨M.X.1.scheme ⨿ N.X.1.scheme,
    (by sorry : Smooth (M.X.1.scheme ⨿ N.X.1.scheme).hom ∧
      Projective (M.X.1.scheme ⨿ N.X.1.scheme).hom)⟩, M.X.2)

/-- The first graph projection from the disjoint union. -/
def sumFst (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    sumAmbient M N ⟶ M.X :=
  Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraph (coprod.inl : M.X.1.scheme ⟶ M.X.1.scheme ⨿ N.X.1.scheme))

/-- The second graph projection from the disjoint union of equally twisted motives. -/
def sumSnd (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) : sumAmbient M N ⟶ N.X :=
  Correspondence.GradedCategory.homOfDegreeZero h
    (Correspondence.rationalGraph (coprod.inr : N.X.1.scheme ⟶ M.X.1.scheme ⨿ N.X.1.scheme))

/-- The first covariant graph inclusion into the disjoint union. -/
def sumInl (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    M.X ⟶ sumAmbient M N :=
  Correspondence.GradedCategory.homOfDegreeZero rfl
    (@Correspondence.rationalOpenGraph k _ M.X.1.scheme (sumAmbient M N).1.scheme _ _ _
      (coprod.inl : M.X.1.scheme ⟶ M.X.1.scheme ⨿ N.X.1.scheme) (by sorry))

/-- The second covariant graph inclusion into the disjoint union of equally twisted motives. -/
def sumInr (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) : N.X ⟶ sumAmbient M N :=
  Correspondence.GradedCategory.homOfDegreeZero h.symm
    (@Correspondence.rationalOpenGraph k _ N.X.1.scheme (sumAmbient M N).1.scheme _ _ _
      (coprod.inr : N.X.1.scheme ⟶ M.X.1.scheme ⨿ N.X.1.scheme) (by sorry))

/-- The direct sum of equally twisted motives, with its block-diagonal projector. -/
def equalTwistSum (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  X := sumAmbient M N
  p := sumFst M N ≫ M.p ≫ sumInl M N + sumSnd M N h ≫ N.p ≫ sumInr M N h
  idem := sorry

/-- The underlying graded object of the equal-twist sum is the disjoint union. -/
theorem equalTwistSum_X
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) : (equalTwistSum M N h).X = sumAmbient M N := rfl

/-- The equal-twist sum has the sum of the two transported projectors. -/
theorem equalTwistSum_p
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) :
    (equalTwistSum M N h).p =
      sumFst M N ≫ M.p ≫ sumInl M N + sumSnd M N h ≫ N.p ≫ sumInr M N h := rfl

/-- Graph inclusions and projections give the bicone for equally twisted motives. -/
def equalTwistBicone (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) : BinaryBicone M N where
  pt := equalTwistSum M N h
  fst := { f := sumFst M N ≫ M.p, comm := by sorry }
  snd := { f := sumSnd M N h ≫ N.p, comm := by sorry }
  inl := { f := M.p ≫ sumInl M N, comm := by sorry }
  inr := { f := N.p ≫ sumInr M N h, comm := by sorry }
  inl_fst := sorry
  inl_snd := sorry
  inr_fst := sorry
  inr_snd := sorry

/-- The first direct-sum projection is the graph projection followed by the first projector. -/
theorem equalTwistBicone_fst_f
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) :
    (equalTwistBicone M N h).fst.f = sumFst M N ≫ M.p := rfl

/-- The first direct-sum inclusion is the first projector followed by its covariant graph. -/
theorem equalTwistBicone_inl_f
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) :
    (equalTwistBicone M N h).inl.f = M.p ≫ sumInl M N := rfl

/-- The two diagonal blocks exhaust the projector on the equal-twist direct sum. -/
theorem equalTwistBicone_total
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) :
    (equalTwistBicone M N h).fst ≫ (equalTwistBicone M N h).inl +
      (equalTwistBicone M N h).snd ≫ (equalTwistBicone M N h).inr =
        𝟙 (equalTwistBicone M N h).pt := sorry

/-- The disjoint-union bicone is a binary biproduct, with explicit lift and descent maps. -/
def equalTwistBiproductData
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))
    (h : M.X.2 = N.X.2) : BinaryBiproductData M N where
  bicone := equalTwistBicone M N h
  isBilimit := isBinaryBilimitOfTotal _ (equalTwistBicone_total M N h)

/-- Replace a motive by an isomorphic representative whose Tate index is one larger,
using one projective-line Lefschetz factor. -/
def raiseTwist (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) :=
  twist
    { X := M.X ⊗ Correspondence.GradedCategory.ofScheme (ProjectiveSpace.schemeOver k 1) 0
      p := M.p ⊗ₘ ((Correspondence.GradedCategory.ProjectiveLine.tateRetract k).r ≫
        (Correspondence.GradedCategory.ProjectiveLine.tateRetract k).i)
      idem := sorry } 1

/-- Cancelling the field-point factor after twisting by one preserves a motive. -/
def twistTensorPointIso (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    twist (M ⊗ tateTwist (SchemeOverField.point k) (-1)) 1 ≅ M where
  hom :=
    { f := (twist (M ⊗ tateTwist (SchemeOverField.point k) (-1)) 1).p ≫
        Correspondence.GradedCategory.homOfDegreeZero
          (X := (twist (M ⊗ tateTwist (SchemeOverField.point k) (-1)) 1).X) (Y := M.X)
          (by change M.X.2 + -1 + 1 = M.X.2; omega)
          (Correspondence.rationalGraphIso _ _
            (Correspondence.GradedCategory.rightUnitorSchemeIso M.X)) ≫ M.p
      comm := sorry }
  inv :=
    { f := M.p ≫ Correspondence.GradedCategory.homOfDegreeZero
        (X := M.X) (Y := (twist (M ⊗ tateTwist (SchemeOverField.point k) (-1)) 1).X)
        (by change M.X.2 = M.X.2 + -1 + 1; omega)
        (Correspondence.rationalGraphIso _ _
          (Correspondence.GradedCategory.rightUnitorSchemeIso M.X).symm) ≫
          (twist (M ⊗ tateTwist (SchemeOverField.point k) (-1)) 1).p
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The explicit Lefschetz-to-Tate comparison identifies the raised representative
with the original motive. -/
def raiseTwistIso (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    raiseTwist M ≅ M :=
  let L := Correspondence.GradedCategory.ofScheme (ProjectiveSpace.schemeOver k 1) 0
  let T := Correspondence.GradedCategory.ofScheme (SchemeOverField.point k) (-1)
  let A : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) :=
    { X := M.X ⊗ L
      p := M.p ⊗ₘ ((Correspondence.GradedCategory.ProjectiveLine.tateRetract k).r ≫
        (Correspondence.GradedCategory.ProjectiveLine.tateRetract k).i)
      idem := sorry }
  let B := M ⊗ tateTwist (SchemeOverField.point k) (-1)
  let e₀ : A ≅ B :=
    { hom :=
        { f := M.p ⊗ₘ (Correspondence.GradedCategory.ProjectiveLine.tateRetract k).r
          comm := sorry }
      inv :=
        { f := M.p ⊗ₘ (Correspondence.GradedCategory.ProjectiveLine.tateRetract k).i
          comm := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }
  (twistFunctor k 1).mapIso e₀ ≪≫ twistTensorPointIso M

/-- Repeatedly replace a motive by its projective-line representative. -/
def raiseTwistIterate (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    ℕ → ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)
  | 0 => M
  | n + 1 => raiseTwist (raiseTwistIterate M n)

/-- Iterated Lefschetz comparisons recover the original motive. -/
def raiseTwistIterateIso (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    (n : ℕ) → raiseTwistIterate M n ≅ M
  | 0 => Iso.refl M
  | n + 1 => raiseTwistIso (raiseTwistIterate M n) ≪≫ raiseTwistIterateIso M n

/-- Each projective-line factor increases the representative's Tate index by one. -/
theorem raiseTwistIterate_index
    (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (n : ℕ) :
    (raiseTwistIterate M n).X.2 = M.X.2 + n := sorry

/-- A binary biproduct of arbitrary motives, formed by raising both Tate indices to
their maximum and taking the disjoint-union direct sum. -/
def binaryBiproductData
    (M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    BinaryBiproductData M N :=
  (equalTwistBiproductData
    (raiseTwistIterate M (max M.X.2 N.X.2 - M.X.2).toNat)
    (raiseTwistIterate N (max M.X.2 N.X.2 - N.X.2).toNat)
    (by rw [raiseTwistIterate_index, raiseTwistIterate_index]; omega)).ofIso
      (raiseTwistIterateIso M _) (raiseTwistIterateIso N _)

/-- The explicit disjoint-union and Lefschetz constructions supply binary biproducts. -/
instance instHasBinaryBiproducts (k : Type u) [Field k] :
    HasBinaryBiproducts (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) where
  has_binary_biproduct M N := HasBinaryBiproduct.mk (binaryBiproductData M N)

/-- Finite products are assembled from the empty-scheme motive and the constructed
binary biproducts. -/
instance instHasFiniteProducts (k : Type u) [Field k] :
    HasFiniteProducts (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The category of Chow motives over a field admits finite biproducts. -/
instance instHasFiniteBiproducts (k : Type u) [Field k] :
    HasFiniteBiproducts
      (ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end ChowMotive
