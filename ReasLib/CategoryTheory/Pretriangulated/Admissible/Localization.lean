/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import ReasLib.CategoryTheory.Pretriangulated.Admissible
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Adjunction
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
    (quotient A).IsLocalization A.rightOrthogonal.trW := sorry

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
    Functor.kernel A.ι.rightAdjoint = A.rightOrthogonal := sorry

/-- Stacks 0H0P: the chosen right adjoint of a right-admissible inclusion is
canonically available as a localization at the right-orthogonal Verdier
system. -/
@[stacks 0H0P]
instance adjointIsLocalization
    (A : ObjectProperty D) [IsRightAdmissible A] :
    A.ι.rightAdjoint.IsLocalization A.rightOrthogonal.trW := sorry

/-- Stacks 0H0P: the canonical right comparison functor is an equivalence. -/
@[stacks 0H0P]
instance comparisonIsEquivalence
    (A : ObjectProperty D) [IsRightAdmissible A] :
    Functor.IsEquivalence (comparison A) := sorry

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
    (quotient A).IsLocalization A.leftOrthogonal.trW := sorry

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
    Functor.kernel A.ι.leftAdjoint = A.leftOrthogonal := sorry

/-- Stacks 0H0P: the chosen left adjoint of a left-admissible inclusion is
canonically available as a localization at the left-orthogonal Verdier
system. -/
@[stacks 0H0P]
instance adjointIsLocalization
    (A : ObjectProperty D) [IsLeftAdmissible A] :
    A.ι.leftAdjoint.IsLocalization A.leftOrthogonal.trW := sorry

/-- Stacks 0H0P: the canonical left comparison functor is an equivalence. -/
@[stacks 0H0P]
instance comparisonIsEquivalence
    (A : ObjectProperty D) [IsLeftAdmissible A] :
    Functor.IsEquivalence (comparison A) := sorry

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
