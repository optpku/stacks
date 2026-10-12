/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.Resolution
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

/-!
# Computing Right Derived Functors from Integer-Indexed Injective Resolutions

Mathlib computes ordinary right derived functors from the native `ℕ`-indexed cocomplex of an
injective resolution.  This file gives the canonical comparison for its `ℤ`-indexed extension,
including the boundary degree `0`.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C]

/-- Every ordinary right derived functor of an additive functor is additive. -/
@[stacks 015J "right derived functors are additive"]
noncomputable instance additive
    (F : C ⥤ D) [F.Additive] (n : ℕ) : (F.rightDerived n).Additive := sorry

/-- An additive functor that preserves homology has zero positive right-derived functors. -/
@[stacks 015J "exact functors have no positive right-derived functors"]
theorem isZero_obj_succ_of_preservesHomology
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (X : C) (n : ℕ) :
    IsZero ((F.rightDerived (n + 1)).obj X) := sorry

end CategoryTheory.Functor.RightDerived

namespace CategoryTheory.InjectiveResolution

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
variable {X : C} (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive]

namespace RightDerived

/-- The mapped integer-indexed injective resolution has zero differential from degree `-1` to
degree `0`. -/
theorem complex_d_negOne_zero :
    ((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).d (-1) 0 = 0 := sorry

/-- The predecessor of degree `0` in an integer-indexed cochain complex is degree `-1`. -/
theorem upInt_prev_zero :
    (up ℤ).prev 0 = (-1 : ℤ) := sorry

/-- In positive degree, the predecessor in a natural-number-indexed cochain complex is the
preceding natural number. -/
theorem upNat_prev_succ (q : ℕ) :
    (up ℕ).prev (q + 1) = q := sorry

/-- In positive degree, the successor in a natural-number-indexed cochain complex is the next
natural number. -/
theorem upNat_next_succ (q : ℕ) :
    (up ℕ).next (q + 1) = q + 2 := sorry

/-- The integer predecessor of a positive natural-number index is its natural predecessor. -/
theorem upInt_prev_ofNat_succ (q : ℕ) :
    (up ℤ).prev (Int.ofNat (q + 1)) = Int.ofNat q := sorry

/-- The integer successor of a positive natural-number index is its natural successor. -/
theorem upInt_next_ofNat_succ (q : ℕ) :
    (up ℤ).next (Int.ofNat (q + 1)) = Int.ofNat (q + 2) := sorry

variable [HasInjectiveResolutions C]

/-- The degree-zero homology of the mapped integer-indexed injective resolution computes the
zeroth right derived functor. -/
noncomputable def homologyIsoZero :
    (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology 0) ≅
      (F.rightDerived 0).obj X :=
  let M := (F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex
  (M.isoHomologyπ (-1) 0 upInt_prev_zero
      (complex_d_negOne_zero I F)).symm ≪≫
    (M.restrictionCyclesIso embeddingUpNat 0 1
      (CochainComplex.next ℕ 0) rfl rfl (CochainComplex.next ℤ 0)).symm ≪≫
    CochainComplex.isoHomologyπ₀ (M.restriction embeddingUpNat) ≪≫
    HomologicalComplex.homologyMapIso (Restriction.Map.iso I F) 0 ≪≫
    (I.isoRightDerivedObj F 0).symm

/-- The positive-degree homology of the mapped integer-indexed injective resolution computes the
corresponding right derived functor. -/
noncomputable def homologyIsoSucc (q : ℕ) :
    (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology
      (Int.ofNat (q + 1))) ≅ (F.rightDerived (q + 1)).obj X :=
  let M := (F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex
  (M.restrictionHomologyIso embeddingUpNat q (q + 1) (q + 2)
      (upNat_prev_succ q) (upNat_next_succ q) rfl rfl rfl
      (upInt_prev_ofNat_succ q) (upInt_next_ofNat_succ q)).symm ≪≫
    HomologicalComplex.homologyMapIso (Restriction.Map.iso I F) (q + 1) ≪≫
    (I.isoRightDerivedObj F (q + 1)).symm

/-- The homology of the mapped `ℤ`-indexed extension of an injective resolution computes the
ordinary right derived functor in every natural degree. -/
@[stacks 015J "integer-indexed injective-resolution right-derived computation"]
noncomputable def homologyIso :
    (q : ℕ) →
      (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology (Int.ofNat q)) ≅
        (F.rightDerived q).obj X
  | 0 => homologyIsoZero I F
  | q + 1 => homologyIsoSucc I F q

/-- The integer-indexed computation agrees with its degree-zero specialization. -/
@[simp]
theorem homologyIso_zero :
    homologyIso I F 0 = homologyIsoZero I F := sorry

/-- The integer-indexed computation agrees with its positive-degree specialization. -/
@[simp]
theorem homologyIso_succ (q : ℕ) :
    homologyIso I F (q + 1) = homologyIsoSucc I F q := sorry

/-- The integer-indexed right-derived computation is natural in a morphism of injective
resolutions. -/
@[reassoc]
theorem homologyIso_hom_naturality
    {Y : C} {J : InjectiveResolution Y} {f : X ⟶ Y}
    (g : Hom I J f) (q : ℕ) :
    HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map g.hom') (Int.ofNat q) ≫
        (homologyIso J F q).hom =
      (homologyIso I F q).hom ≫
        (F.rightDerived q).map f := sorry

/-- Inverse form of the naturality of the integer-indexed right-derived computation. -/
@[reassoc]
theorem homologyIso_inv_naturality
    {Y : C} {J : InjectiveResolution Y} {f : X ⟶ Y}
    (g : Hom I J f) (q : ℕ) :
    (homologyIso I F q).inv ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map g.hom') (Int.ofNat q) =
      (F.rightDerived q).map f ≫
        (homologyIso J F q).inv := sorry

end RightDerived

end CategoryTheory.InjectiveResolution
