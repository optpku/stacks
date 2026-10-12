/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Exactness
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B)

/- Lemma 12.7.2 [010N] (1): a left exact or right exact functor between
abelian categories is additive. -/
@[stacks 010N]
#check (F.additive_of_leftExact_or_rightExact :
  leftExactFunctor A B F ∨ rightExactFunctor A B F → F.Additive)

/- Lemma 12.7.2 [010N] (2): left exactness is detected on short exact
complexes by exactness of the image pair and monicity of its first map. -/
@[stacks 010N]
#check (F.leftExact_iff_maps_shortExact :
  leftExactFunctor A B F ↔
    ∀ S : ShortComplex A, S.ShortExact →
      (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧ Mono (F.map S.f))

/- Lemma 12.7.2 [010N] (3): right exactness is detected on short exact
complexes by exactness of the image pair and epicity of its second map. -/
@[stacks 010N]
#check (F.rightExact_iff_maps_shortExact :
  rightExactFunctor A B F ↔
    ∀ S : ShortComplex A, S.ShortExact →
      (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧ Epi (F.map S.g))

/- Lemma 12.7.2 [010N] (4): exactness is detected by sending every short
exact complex to an exact pair with monic first and epic second map. -/
@[stacks 010N]
#check (F.exact_iff_maps_shortExact :
  exactFunctor A B F ↔
    ∀ S : ShortComplex A, S.ShortExact →
      (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
        Mono (F.map S.f) ∧ Epi (F.map S.g))

end CategoryTheory
