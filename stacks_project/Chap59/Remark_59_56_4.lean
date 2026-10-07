module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap58.Lemma_58_2_2
public import stacks_project.Chap59.Theorem_59_56_3
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/- Sites Definition 7.12.3 is Yoneda representability of a
contravariant set-valued functor. -/
@[stacks 04JL] #check Functor.IsRepresentable

/-- Remark 59.56.4 (1): combining Theorem 59.56.3 with Fundamental Groups,
Lemma 58.2.2, every sheaf on `Spec K` étale is represented by some scheme
étale over `Spec K`. -/
@[stacks 04JL]
theorem sheaf_isRepresentableByEtaleScheme
    (K : Type u) [Field K] (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    F.obj.IsRepresentable := sorry

/-- Remark 59.56.4 (2): this is not Sites Definition 7.12.3 representability on a
merely chosen small subcategory of schemes étale over `Spec K`. If
`ι : C ⥤ (Spec K).Etale` is fully faithful and not essentially surjective, some
sheaf on the small étale site is not represented by any object in the image of
`ι`. -/
@[stacks 04JL]
theorem not_isRepresentable_of_not_essSurj
    {C : Type v} [Category.{u} C] (K : Type u) [Field K]
    (ι : C ⥤ (Spec (.of K)).Etale) (hff : ι.FullyFaithful) (hι : ¬ Functor.EssSurj ι) :
    ∃ F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u),
      ∀ c : C, ¬ Nonempty (F.obj.RepresentableBy (ι.obj c)) := sorry

end AlgebraicGeometry.Scheme.Etale
