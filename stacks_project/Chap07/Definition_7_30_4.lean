/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.SheafLocalization
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type (max u v)))

/-- Align the canonical monoidal closed structure with the Cartesian structure used by sections. -/
-- Local instance justification (defeq pin): the generic localization requires the sheaf monoidal closed structure over the inferred Cartesian monoidal structure.
private noncomputable instance sheafSectionsClosed :
    @MonoidalClosed (Sheaf J (Type (max u v))) inferInstance
      (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toMonoidalCategory :=
  let closedSheaf : MonoidalClosed (Sheaf J (Type (max u v))) := inferInstance
  closedSheaf

/-- Use the canonical Cartesian braiding for the sections adjunction. -/
-- Local instance justification (defeq pin): the sections adjunction requires the braiding of the same Cartesian monoidal structure as its internal hom.
private noncomputable instance sheafSectionsBraided :
    @BraidedCategory (Sheaf J (Type (max u v))) inferInstance
      (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toMonoidalCategory :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- The sections construction uses the canonical pullbacks in the sheaf category. -/
-- Local instance justification (noncanonical choice): specialize the generic sections construction using the standard limit-based choice of pullbacks.
private noncomputable instance sheafSectionsChosenPullbacks :
    ChosenPullbacksAlong (curryRightUnitorHom ℱ) :=
  ChosenPullbacksAlong.ofHasPullbacksAlong _

/- Definition 7.30.4: the topos `Over ℱ` is the localization of the topos `Sh(C, J)` at `ℱ`,
and the localization morphism is the canonical left-exact adjunction whose inverse image is
`Over.star ℱ` and whose direct image is the sections functor. -/
@[stacks 04IP] #check (CategoryTheory.LeftExactAdjunction.sheafLocalization ℱ :
  LeftExactAdjunction (Over ℱ) (Sheaf J (Type (max u v))))

/- The localization carrier is the slice category over `ℱ`. -/
#check (CategoryTheory.Over ℱ : Type (max u v + 1))

/- Companion recall: `Over.forgetAdjStar ℱ` is the lower-shriek adjunction
`Over.forget ℱ ⊣ Over.star ℱ`, not the localization morphism itself. -/
#check (Over.forgetAdjStar ℱ : Over.forget ℱ ⊣ Over.star ℱ)

/- The lower-shriek functor of the localization morphism is the slice forgetful functor. -/
#check (Over.forget ℱ : Over ℱ ⥤ Sheaf J (Type (max u v)))

/- The inverse-image functor of the localization morphism is `Over.star ℱ`. -/
#check (Over.star ℱ : Sheaf J (Type (max u v)) ⥤ Over ℱ)
