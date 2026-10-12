/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend

@[expose] public section

/-!
# Integer-Indexed Views of Injective Resolutions

This file compares Mathlib's native `ℕ`-indexed injective-resolution cocomplex with its
extension to an `ℤ`-indexed cochain complex.  The comparison is independent of derived functors.
-/

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.InjectiveResolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {X : C} (I : InjectiveResolution X)

namespace Restriction

/-- The component comparing the restriction of the integer-indexed extension with the original
injective-resolution cocomplex. -/
noncomputable abbrev componentIso (n : ℕ) :
    (I.cochainComplex.restriction embeddingUpNat).X n ≅ I.cocomplex.X n :=
  I.cochainComplex.restrictionXIso embeddingUpNat
      (i := n) (i' := Int.ofNat n) rfl ≪≫
    I.cochainComplexXIso (Int.ofNat n) n rfl

/-- The components of `iso` commute with the differentials. -/
theorem componentIso_comm (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    (componentIso I i).hom ≫ I.cocomplex.d i j =
      (I.cochainComplex.restriction embeddingUpNat).d i j ≫
        (componentIso I j).hom := sorry

/-- Restricting the integer-indexed extension of an injective resolution along
`embeddingUpNat` recovers its native cocomplex. -/
noncomputable def iso :
    I.cochainComplex.restriction embeddingUpNat ≅ I.cocomplex :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso I)
    (componentIso_comm I)

/-- The components of `iso` are the canonical restriction and extension
comparisons. -/
@[simp]
theorem iso_hom_f (n : ℕ) :
    (iso I).hom.f n = (componentIso I n).hom := sorry

/-- The inverse components of `iso` are the canonical restriction and
extension comparisons. -/
@[simp]
theorem iso_inv_f (n : ℕ) :
    (iso I).inv.f n = (componentIso I n).inv := sorry

/-- The restriction comparison is natural in a morphism of injective resolutions. -/
@[reassoc]
theorem iso_hom_naturality
    {Y : C} {J : InjectiveResolution Y} {f : X ⟶ Y}
    (g : Hom I J f) :
    HomologicalComplex.restrictionMap g.hom' embeddingUpNat ≫
        (iso J).hom =
      (iso I).hom ≫ g.hom := sorry

namespace Map

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- After applying an additive functor, restricting the mapped integer-indexed resolution
recovers the mapped native cocomplex. -/
noncomputable def iso
    (F : C ⥤ D) [F.Additive] :
    (((F.mapHomologicalComplex (up ℤ)).obj I.cochainComplex).restriction embeddingUpNat) ≅
      ((F.mapHomologicalComplex (up ℕ)).obj I.cocomplex) :=
  (F.mapHomologicalComplex (up ℕ)).mapIso (Restriction.iso I)

/-- The mapped restriction comparison is natural in a morphism of injective resolutions. -/
@[reassoc]
theorem iso_hom_naturality
    (F : C ⥤ D) [F.Additive]
    {Y : C} {J : InjectiveResolution Y} {f : X ⟶ Y}
    (g : Hom I J f) :
    HomologicalComplex.restrictionMap
          ((F.mapHomologicalComplex (up ℤ)).map g.hom') embeddingUpNat ≫
        (iso J F).hom =
      (iso I F).hom ≫
        (F.mapHomologicalComplex (up ℕ)).map g.hom := sorry

end Map

end Restriction

end CategoryTheory.InjectiveResolution
