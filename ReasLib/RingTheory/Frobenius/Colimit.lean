/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.RingTheory.Seminormal.Perfect

/-!
# Frobenius colimits of rings

This module constructs the sequential colimit of a commutative `ZMod p`-algebra under
Frobenius, together with its canonical maps and ring-theoretic properties.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Ring.FrobeniusColimit

/-- A prime `p` acts by zero on every commutative `ZMod p`-algebra. -/
theorem primeCast_eq_zero (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) A) p,
    CharP.cast_eq_zero (ZMod p) p, map_zero]

/-- The Frobenius endomorphism of a commutative `ZMod p`-algebra. -/
def frobenius (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : A →+* A :=
  RingHom.frobeniusOfPrime p (primeCast_eq_zero p A)

/-- Frobenius sends an element to its `p`-th power. -/
theorem frobenius_apply (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (x : A) :
    frobenius p A x = x ^ p := rfl

/-- The sequential diagram consisting of copies of `A` joined by Frobenius. -/
def diagram (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (fun _ : ℕ ↦
    (CommRingCat.ofHom (frobenius p A) : CommRingCat.of A ⟶ CommRingCat.of A))

/-- Every object of the Frobenius diagram is the original commutative ring. -/
theorem diagram_obj (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    (diagram p A).obj n = CommRingCat.of A := rfl

/-- Every successor map in the sequential diagram is Frobenius. -/
theorem diagram_map_succ (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    (diagram p A).map (homOfLE n.le_succ) = CommRingCat.ofHom (frobenius p A) := by
  simpa [diagram] using
    (Functor.ofSequence_map_homOfLE_succ
      (f := fun _ : ℕ =>
        (CommRingCat.ofHom (frobenius p A) : CommRingCat.of A ⟶ CommRingCat.of A)) n)

/-- The colimit of a commutative `ZMod p`-algebra under repeated Frobenius. -/
noncomputable def ring (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : CommRingCat.{u} :=
  colimit (diagram p A)

/-- The canonical morphism from the `n`-th Frobenius stage to the colimit. -/
noncomputable def ι (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    CommRingCat.of A ⟶ ring p A :=
  colimit.ι (diagram p A) n

/-- Successive canonical stage maps are compatible with Frobenius. -/
theorem ι_succ (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    CommRingCat.ofHom (frobenius p A) ≫ ι p A (n + 1) = ι p A n := by
  unfold ι
  rw [← diagram_map_succ p A n]
  exact colimit.w (diagram p A) (homOfLE n.le_succ)

/-- The underlying ring homomorphism from the initial stage to the Frobenius colimit. -/
noncomputable def toRingHom (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : A →+* ring p A :=
  (ι p A 0).hom

/-- The initial-stage map equips the Frobenius colimit with its canonical `A`-algebra structure. -/
noncomputable instance instAlgebra (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : Algebra A (ring p A) :=
  (toRingHom p A).toAlgebra

/-- The algebra map into the Frobenius colimit is its initial-stage ring homomorphism. -/
theorem algebraMap_eq_toRingHom (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    algebraMap A (ring p A) = toRingHom p A := by
  exact RingHom.algebraMap_toAlgebra (toRingHom p A)

/-- The sequential Frobenius colimit is perfect. -/
noncomputable instance instPerfectRing (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : PerfectRing (ring p A) p := by
  have hp : (p : ring p A) = 0 := by
    rw [← map_natCast (toRingHom p A) p, primeCast_eq_zero p A, map_zero]
  let shifted : Cocone (diagram p A) :=
    { pt := ring p A
      ι :=
        NatTrans.ofSequence
          (fun n => ι p A (n + 1))
          (fun n => by
            rw [diagram_map_succ p A n]
            change CommRingCat.ofHom (frobenius p A) ≫ ι p A (n + 1 + 1) =
              ι p A (n + 1) ≫ 𝟙 _
            rw [ι_succ, Category.comp_id]) }
  let shift : ring p A ⟶ ring p A := colimit.desc (diagram p A) shifted
  let F : ring p A ⟶ ring p A :=
    CommRingCat.ofHom (RingHom.frobeniusOfPrime p hp)
  have hF (n : ℕ) :
      ι p A n ≫ F = CommRingCat.ofHom (frobenius p A) ≫ ι p A n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change ((ι p A n).hom x) ^ p = (ι p A n).hom (x ^ p)
    exact (map_pow (ι p A n).hom x p).symm
  have hshift (n : ℕ) :
      ι p A n ≫ shift = ι p A (n + 1) := by
    exact colimit.ι_desc shifted n
  have hleft : F ≫ shift = 𝟙 _ := by
    apply colimit.hom_ext (F := diagram p A)
    intro n
    calc
      ι p A n ≫ (F ≫ shift) = (ι p A n ≫ F) ≫ shift :=
        (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom (frobenius p A) ≫ ι p A n) ≫ shift := by
        rw [hF n]
      _ = CommRingCat.ofHom (frobenius p A) ≫ (ι p A n ≫ shift) :=
        Category.assoc _ _ _
      _ = CommRingCat.ofHom (frobenius p A) ≫ ι p A (n + 1) := by
        rw [hshift n]
      _ = ι p A n := ι_succ p A n
      _ = ι p A n ≫ 𝟙 _ := (Category.comp_id _).symm
  have hright : shift ≫ F = 𝟙 _ := by
    apply colimit.hom_ext (F := diagram p A)
    intro n
    calc
      ι p A n ≫ (shift ≫ F) = (ι p A n ≫ shift) ≫ F :=
        (Category.assoc _ _ _).symm
      _ = ι p A (n + 1) ≫ F := by
        rw [hshift n]
      _ = CommRingCat.ofHom (frobenius p A) ≫ ι p A (n + 1) := hF (n + 1)
      _ = ι p A n := ι_succ p A n
      _ = ι p A n ≫ 𝟙 _ := (Category.comp_id _).symm
  refine ⟨Function.bijective_iff_has_inverse.mpr ⟨shift.hom, ?_, ?_⟩⟩
  · intro x
    have hx := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hleft) x
    change shift.hom (x ^ p) = x at hx
    exact hx
  · intro x
    have hx := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hright) x
    change (shift.hom x) ^ p = x at hx
    exact hx

/-- The sequential Frobenius colimit is absolutely weakly normal. -/
noncomputable instance instAbsolutelyWeaklyNormalRing (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    AbsolutelyWeaklyNormalRing (ring p A) := by
  letI : Algebra (ZMod p) (ring p A) :=
    RingHom.toAlgebra ((algebraMap A (ring p A)).comp (algebraMap (ZMod p) A))
  exact (absolutelyWeaklyNormalRing_iff_perfectRing p (ring p A)).2 inferInstance

end Ring.FrobeniusColimit
