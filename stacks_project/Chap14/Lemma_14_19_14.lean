module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Over
import StacksCheckRecall

/-!
@stack 08NJ

# Lemma 14.19.14 compatibility facade

The reusable owner is the natural isomorphism `Over.forget.coskeleton.iso`; finite limits imply its
finite-connected-limit hypothesis, and `NeZero k` is the typeclass form of the source condition
`1 ≤ k`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable (X : C) (k : ℕ) [NeZero k]

/- Lemma 14.19.14: the forgetful functor `Over X ⥤ C` commutes naturally with the
`k`-coskeleton functors for `k ≥ 1`. -/
@[stacks 08NJ]
#check (Over.forget.coskeleton.iso X k :
  (Truncated.cosk k :
      SimplicialObject.Truncated (Over X) k ⥤ SimplicialObject (Over X)) ⋙
        (SimplicialObject.whiskering (Over X) C).obj (Over.forget X) ≅
    (SimplicialObject.Truncated.whiskering (Over X) C).obj (Over.forget X) ⋙
      (Truncated.cosk k : SimplicialObject.Truncated C k ⥤ SimplicialObject C))

/- The component API directly identifies the two coskeletons of a truncated simplicial object. -/
#check Over.forget.coskeleton.isoApp X k

/- The comparison is characterized by compatibility with the right-Kan-extension counit. -/
#check Over.forget.coskeleton.isoApp.hom_counit X k

/- The inverse comparison satisfies the symmetric counit formula. -/
#check Over.forget.coskeleton.isoApp.inv_counit X k

end CategoryTheory
