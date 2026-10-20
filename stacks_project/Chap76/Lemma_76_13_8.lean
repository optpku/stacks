module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting.Cancellation
import StacksCheckRecall

/-!
# Cancellation of formally smooth, étale, and unramified transformations

If `b : G ⟶ H` is formally unramified, then formal unramifiedness, étaleness, or
smoothness of `b ∘ a` implies the same property of `a`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over

universe u v

/- Lemma 76.13.8 (1): If `b` is formally unramified and `b ∘ a` is formally
unramified, then `a` is formally unramified. -/
@[stacks 04G5]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.of_comp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (b : G ⟶ H)
      [FormallyUnramified b] [FormallyUnramified (a ≫ b)], FormallyUnramified a)

/- Lemma 76.13.8 (2): If `b` is formally unramified and `b ∘ a` is formally
étale, then `a` is formally étale. -/
@[stacks 04G5]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.of_comp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (b : G ⟶ H)
      [FormallyUnramified b] [FormallyEtale (a ≫ b)], FormallyEtale a)

/- Lemma 76.13.8 (3): If `b` is formally unramified and `b ∘ a` is formally
smooth, then `a` is formally smooth. -/
@[stacks 04G5]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.of_comp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (b : G ⟶ H)
      [FormallyUnramified b] [FormallySmooth (a ≫ b)], FormallySmooth a)
