module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Direct
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.OfHomQuasiInverse
import Mathlib.Tactic.CrossRefAttribute

/-!
# Components of inverse-image morphism comparisons

This leaf exposes the forward and inverse components of the comparison and choice-independence
isomorphisms for both explicit presentations of inverse image on stack-morphism categories.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable {u : C ⥤ D}

section Direct

variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
variable (I : StackOver.InverseImage K u S)
variable (I' : StackOver.InverseImage K u S')
variable (h_pushforward : FiberedCategoryOver.Pushforward.InversionChoice u
  S.toFiberedCategoryOver S'.toFiberedCategoryOver)

namespace mapHom.comparisonIso.hom

/-- The forward component of the direct inverse-image comparison is the chosen counit at the
pushforward of `F`, postcomposed with the target stackification comparison. -/
@[simp, stacks 04WS "direct comparison forward component"]
theorem app
    (q : Functor.QuasiInverse (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (mapHom.comparisonIso I I' h_pushforward q).hom.app F =
      q.counitIso.hom.app
        ((StackOver.Pushforward.mapFunctor u h_pushforward).obj F ≫ I'.comparisonHom) := sorry

end mapHom.comparisonIso.hom

namespace mapHom.comparisonIso.inv

/-- The inverse component of the direct inverse-image comparison is the inverse chosen counit at
the pushforward of `F`, postcomposed with the target stackification comparison. -/
@[simp, stacks 04WS "direct comparison inverse component"]
theorem app
    (q : Functor.QuasiInverse (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (mapHom.comparisonIso I I' h_pushforward q).inv.app F =
      q.counitIso.inv.app
        ((StackOver.Pushforward.mapFunctor u h_pushforward).obj F ≫ I'.comparisonHom) := sorry

end mapHom.comparisonIso.inv

namespace mapHom.choiceIso.hom

/-- The forward component comparing two direct inverse-image lifts is the canonical comparison
of their chosen inverse functors at the pushed-forward postcomposite. -/
@[simp, stacks 04WS "direct choice comparison forward component"]
theorem app
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (mapHom.choiceIso I I' h_pushforward q q').hom.app F =
      (q.inverseIso q').hom.app
        ((StackOver.Pushforward.mapFunctor u h_pushforward).obj F ≫ I'.comparisonHom) := sorry

end mapHom.choiceIso.hom

namespace mapHom.choiceIso.inv

/-- The inverse component comparing two direct inverse-image lifts is the inverse canonical
comparison of their chosen inverse functors at the pushed-forward postcomposite. -/
@[simp, stacks 04WS "direct choice comparison inverse component"]
theorem app
    (q q' : Functor.QuasiInverse (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (mapHom.choiceIso I I' h_pushforward q q').inv.app F =
      (q.inverseIso q').inv.app
        ((StackOver.Pushforward.mapFunctor u h_pushforward).obj F ≫ I'.comparisonHom) := sorry

end mapHom.choiceIso.inv

end Direct

section OfHomQuasiInverse

variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]
variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
variable (I : StackOver.InverseImage K u S)
variable (I' : StackOver.InverseImage K u S')

namespace mapHom.ofHomQuasiInverse.comparisonIso.hom

set_option maxHeartbeats 400000 in
/-- The forward comparison component for the Hom-quasi-inverse presentation is the chosen
counit at `F ≫ pullbackComparison I'`. -/
@[simp, stacks 04WS "Hom-quasi-inverse comparison forward component"]
theorem app (q : Functor.QuasiInverse (homFunctor I I'.target)) (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse.comparisonIso I I' q).hom.app F =
      q.counitIso.hom.app (F ≫ pullbackComparison I') := sorry

end mapHom.ofHomQuasiInverse.comparisonIso.hom

namespace mapHom.ofHomQuasiInverse.comparisonIso.inv

/-- The inverse comparison component for the Hom-quasi-inverse presentation is the inverse
chosen counit at `F ≫ pullbackComparison I'`. -/
@[simp, stacks 04WS "Hom-quasi-inverse comparison inverse component"]
theorem app (q : Functor.QuasiInverse (homFunctor I I'.target)) (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse.comparisonIso I I' q).inv.app F =
      q.counitIso.inv.app (F ≫ pullbackComparison I') := sorry

end mapHom.ofHomQuasiInverse.comparisonIso.inv

namespace mapHom.ofHomQuasiInverse.choiceIso.hom

/-- The forward component comparing two Hom-quasi-inverse presentations is the canonical
comparison of their inverse functors at `F ≫ pullbackComparison I'`. -/
@[simp, stacks 04WS "Hom-quasi-inverse choice forward component"]
theorem app (q q' : Functor.QuasiInverse (homFunctor I I'.target)) (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse.choiceIso I I' q q').hom.app F =
      (q.inverseIso q').hom.app (F ≫ pullbackComparison I') := sorry

end mapHom.ofHomQuasiInverse.choiceIso.hom

namespace mapHom.ofHomQuasiInverse.choiceIso.inv

/-- The inverse component comparing two Hom-quasi-inverse presentations is the inverse canonical
comparison of their inverse functors at `F ≫ pullbackComparison I'`. -/
@[simp, stacks 04WS "Hom-quasi-inverse choice inverse component"]
theorem app (q q' : Functor.QuasiInverse (homFunctor I I'.target)) (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse.choiceIso I I' q q').inv.app F =
      (q.inverseIso q').inv.app (F ≫ pullbackComparison I') := sorry

end mapHom.ofHomQuasiInverse.choiceIso.inv

end OfHomQuasiInverse

end StackOver.InverseImage

end CategoryTheory
