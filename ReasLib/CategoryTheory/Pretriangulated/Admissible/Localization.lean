/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import ReasLib.CategoryTheory.Pretriangulated.Admissible
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localization by Orthogonals of Admissible Subcategories

The comparison with a Verdier quotient is owned by the admissible subcategory,
while the quotient itself remains the canonical localization supplied by the
object property.  Named comparison functors keep downstream statements short.
-/

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.ObjectProperty.Admissible

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Right

/-- The canonical Verdier quotient functor associated to the right orthogonal
of `A`. -/
@[stacks 0H0P]
abbrev quotient (A : ObjectProperty D) : D ⥤ D / A.rightOrthogonal :=
  A.rightOrthogonal.trW.Q

/-- The named right-orthogonal quotient retains the canonical localization
instance of the underlying Verdier quotient functor. -/
instance quotientIsLocalization (A : ObjectProperty D) :
    (quotient A).IsLocalization A.rightOrthogonal.trW :=
  Functor.q_isLocalization A.rightOrthogonal.trW

/-- The canonical comparison from a subcategory to the Verdier quotient by
its right orthogonal. -/
@[stacks 0H0P]
abbrev comparison (A : ObjectProperty D) :
    A.FullSubcategory ⥤ D / A.rightOrthogonal :=
  A.ι ⋙ quotient A

/-- Stacks 0H0P: the kernel of the chosen right adjoint to a right-admissible
inclusion is its right orthogonal. -/
@[stacks 0H0P]
theorem kernel_eq (A : ObjectProperty D) [IsRightAdmissible A] :
    Functor.kernel A.ι.rightAdjoint = A.rightOrthogonal := by
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  ext X
  change IsZero (A.ι.rightAdjoint.obj X) ↔ A.rightOrthogonal X
  constructor
  · intro h Y f hY
    apply (adj.homEquiv ⟨Y, hY⟩ X).injective
    exact (h.eq_zero_of_tgt _).trans (adj.homAddEquiv_zero ⟨Y, hY⟩ X).symm
  · intro h
    rw [IsZero.iff_id_eq_zero]
    apply (adj.homEquiv (A.ι.rightAdjoint.obj X) X).symm.injective
    exact (h _ (A.ι.rightAdjoint.obj X).property).trans
      (adj.homAddEquiv_symm_zero (A.ι.rightAdjoint.obj X) X).symm

/-- Stacks 0H0P: the chosen right adjoint of a right-admissible inclusion is
canonically available as a localization at the right-orthogonal Verdier
system. -/
@[stacks 0H0P]
instance adjointIsLocalization
    (A : ObjectProperty D) [IsRightAdmissible A] :
    A.ι.rightAdjoint.IsLocalization A.rightOrthogonal.trW := by
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  letI := adj.isTriangulated_rightAdjoint
  have hW : A.rightOrthogonal.trW =
      (MorphismProperty.isomorphisms A.FullSubcategory).inverseImage A.ι.rightAdjoint := by
    ext X Y f
    obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    refine (A.rightOrthogonal.trW_iff_of_distinguished (Triangle.mk f g h) hT).trans ?_
    rw [← kernel_eq A]
    exact (A.ι.rightAdjoint.mapTriangle.obj (Triangle.mk f g h)).isZero₃_iff_isIso₁
      (A.ι.rightAdjoint.map_distinguished _ hT)
  rw [hW]
  exact adj.isLocalization'

/-- Stacks 0H0P: the canonical right comparison functor is an equivalence. -/
@[stacks 0H0P]
instance comparisonIsEquivalence
    (A : ObjectProperty D) [IsRightAdmissible A] :
    Functor.IsEquivalence (comparison A) := by
  let e := Localization.uniq A.ι.rightAdjoint (quotient A) A.rightOrthogonal.trW
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  let i : e.functor ≅ comparison A :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.unit) e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.rightAdjoint (quotient A) A.rightOrthogonal.trW)
  exact Functor.isEquivalence_of_iso i

/-- Stacks 0H0P: the canonical factorization of the right adjoint through the
Verdier quotient and a quasi-inverse of the comparison equivalence. -/
@[stacks 0H0P]
noncomputable def adjointIso
    (A : ObjectProperty D) [IsRightAdmissible A] :
    A.ι.rightAdjoint ≅ quotient A ⋙ (comparison A).asEquivalence.inverse :=
  let e : A.FullSubcategory ≌ D / A.rightOrthogonal :=
    Localization.uniq A.ι.rightAdjoint (quotient A) A.rightOrthogonal.trW
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  let i : e.functor ≅ comparison A :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.unit) e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.rightAdjoint (quotient A) A.rightOrthogonal.trW)
  let j : e.inverse ≅ (comparison A).asEquivalence.inverse :=
    Adjunction.rightAdjointUniq (e.changeFunctor i).toAdjunction
      (comparison A).asEquivalence.toAdjunction
  (Localization.compUniqInverse A.ι.rightAdjoint (quotient A) A.rightOrthogonal.trW).symm ≪≫
    Functor.isoWhiskerLeft (quotient A) j

end Right

namespace Left

/-- The canonical Verdier quotient functor associated to the left orthogonal
of `A`. -/
@[stacks 0H0P]
abbrev quotient (A : ObjectProperty D) : D ⥤ D / A.leftOrthogonal :=
  A.leftOrthogonal.trW.Q

/-- The named left-orthogonal quotient retains the canonical localization
instance of the underlying Verdier quotient functor. -/
instance quotientIsLocalization (A : ObjectProperty D) :
    (quotient A).IsLocalization A.leftOrthogonal.trW :=
  Functor.q_isLocalization A.leftOrthogonal.trW

/-- The canonical comparison from a subcategory to the Verdier quotient by
its left orthogonal. -/
@[stacks 0H0P]
abbrev comparison (A : ObjectProperty D) :
    A.FullSubcategory ⥤ D / A.leftOrthogonal :=
  A.ι ⋙ quotient A

/-- Stacks 0H0P: the kernel of the chosen left adjoint to a left-admissible
inclusion is its left orthogonal. -/
@[stacks 0H0P]
theorem kernel_eq (A : ObjectProperty D) [IsLeftAdmissible A] :
    Functor.kernel A.ι.leftAdjoint = A.leftOrthogonal := by
  let adj : A.ι.leftAdjoint ⊣ A.ι := Adjunction.ofIsRightAdjoint A.ι
  letI := adj.left_adjoint_additive
  ext X
  change IsZero (A.ι.leftAdjoint.obj X) ↔ A.leftOrthogonal X
  constructor
  · intro h Y f hY
    apply (adj.homEquiv X ⟨Y, hY⟩).symm.injective
    exact (h.eq_zero_of_src _).trans (adj.homAddEquiv_symm_zero X ⟨Y, hY⟩).symm
  · intro h
    rw [IsZero.iff_id_eq_zero]
    apply (adj.homEquiv X (A.ι.leftAdjoint.obj X)).injective
    exact (h _ (A.ι.leftAdjoint.obj X).property).trans
      (adj.homAddEquiv_zero X (A.ι.leftAdjoint.obj X)).symm

/-- Stacks 0H0P: the chosen left adjoint of a left-admissible inclusion is
canonically available as a localization at the left-orthogonal Verdier
system. -/
@[stacks 0H0P]
instance adjointIsLocalization
    (A : ObjectProperty D) [IsLeftAdmissible A] :
    A.ι.leftAdjoint.IsLocalization A.leftOrthogonal.trW := by
  let adj : A.ι.leftAdjoint ⊣ A.ι := Adjunction.ofIsRightAdjoint A.ι
  letI := adj.leftAdjointCommShift ℤ
  letI := adj.commShift_of_rightAdjoint ℤ
  letI := adj.isTriangulated_leftAdjoint
  have hW : A.leftOrthogonal.trW =
      (MorphismProperty.isomorphisms A.FullSubcategory).inverseImage A.ι.leftAdjoint := by
    ext X Y f
    obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    refine (A.leftOrthogonal.trW_iff_of_distinguished (Triangle.mk f g h) hT).trans ?_
    rw [← kernel_eq A]
    exact (A.ι.leftAdjoint.mapTriangle.obj (Triangle.mk f g h)).isZero₃_iff_isIso₁
      (A.ι.leftAdjoint.map_distinguished _ hT)
  rw [hW]
  exact adj.isLocalization

/-- Stacks 0H0P: the canonical left comparison functor is an equivalence. -/
@[stacks 0H0P]
instance comparisonIsEquivalence
    (A : ObjectProperty D) [IsLeftAdmissible A] :
    Functor.IsEquivalence (comparison A) := by
  let e := Localization.uniq A.ι.leftAdjoint (quotient A) A.leftOrthogonal.trW
  let adj : A.ι.leftAdjoint ⊣ A.ι := Adjunction.ofIsRightAdjoint A.ι
  let i : e.functor ≅ comparison A :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit).symm e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.leftAdjoint (quotient A) A.leftOrthogonal.trW)
  exact Functor.isEquivalence_of_iso i

/-- Stacks 0H0P: the canonical factorization of the left adjoint through the
Verdier quotient and a quasi-inverse of the comparison equivalence. -/
@[stacks 0H0P]
noncomputable def adjointIso
    (A : ObjectProperty D) [IsLeftAdmissible A] :
    A.ι.leftAdjoint ≅ quotient A ⋙ (comparison A).asEquivalence.inverse :=
  let e : A.FullSubcategory ≌ D / A.leftOrthogonal :=
    Localization.uniq A.ι.leftAdjoint (quotient A) A.leftOrthogonal.trW
  let adj : A.ι.leftAdjoint ⊣ A.ι := Adjunction.ofIsRightAdjoint A.ι
  let i : e.functor ≅ comparison A :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit).symm e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.leftAdjoint (quotient A) A.leftOrthogonal.trW)
  let j : e.inverse ≅ (comparison A).asEquivalence.inverse :=
    Adjunction.rightAdjointUniq (e.changeFunctor i).toAdjunction
      (comparison A).asEquivalence.toAdjunction
  (Localization.compUniqInverse A.ι.leftAdjoint (quotient A) A.leftOrthogonal.trW).symm ≪≫
    Functor.isoWhiskerLeft (quotient A) j

end Left

end CategoryTheory.ObjectProperty.Admissible
