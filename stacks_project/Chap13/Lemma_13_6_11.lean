module

import ReasLib.CategoryTheory.Functor.HomologicalKernel.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [Functor.IsHomological H]

/- Lemma 13.6.11: a homological functor inverts exactly the Verdier system attached to its
homological kernel, hence admits the canonical localization factorization. -/
@[stacks 05RM] #check
  (Functor.homologicalKernel_trW_isInvertedBy H :
    H.homologicalKernel.trW.IsInvertedBy H)

/- The source's strictly full saturated triangulated subcategory is represented by the canonical
object property `H.homologicalKernel` and its reusable closure instances. -/
#check (inferInstance : H.homologicalKernel.IsClosedUnderIsomorphisms)
#check (inferInstance : H.homologicalKernel.IsStableUnderRetracts)
#check (inferInstance : H.homologicalKernel.IsTriangulated)

/- The shifted-map characterization identifies the source's displayed class of arrows with the
cone-defined Verdier system. -/
#check Functor.mem_homologicalKernel_trW_iff

/- The localization lift and its factorization equation are obtained directly from the strict
universal property; no chapter-local factorization datum is needed. -/
#check
  (Localization.strictUniversalPropertyFixedTargetQ H.homologicalKernel.trW A).lift
    H (Functor.homologicalKernel_trW_isInvertedBy H)

#check
  (Localization.strictUniversalPropertyFixedTargetQ H.homologicalKernel.trW A).fac
    H (Functor.homologicalKernel_trW_isInvertedBy H)

end CategoryTheory
