/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Invariance under parallel morphisms

Invariance is expressed by forward factorization, a commuting isomorphism of pullbacks,
or equality of pulled-back subobjects.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {R U T : C}

namespace Morphism

/-- An arrow is forward invariant under `s` and `t` when the target map restricted to
its pullback along `s` factors through that arrow. -/
def IsForwardInvariant (s t : R ⟶ U) (i : T ⟶ U) : Prop :=
  ∃ h : pullback i s ⟶ T, h ≫ i = pullback.snd i s ≫ t

/-- Forward invariance means that every arrow into the relation object whose source
composite factors through `i` also has its target composite factoring through `i`. -/
theorem isForwardInvariant_iff (s t : R ⟶ U) (i : T ⟶ U) :
    IsForwardInvariant s t i ↔
      ∀ {X : C} (r : X ⟶ R),
        (∃ hs : X ⟶ T, hs ≫ i = r ≫ s) →
          ∃ ht : X ⟶ T, ht ≫ i = r ≫ t := sorry

/-- An arrow is pullback invariant under `s` and `t` when its two pullbacks are
isomorphic by an isomorphism commuting with the projections to the relation object. -/
def IsPullbackInvariant (s t : R ⟶ U) (i : T ⟶ U) : Prop :=
  ∃ e : pullback i t ≅ pullback i s,
    e.hom ≫ pullback.snd i s = pullback.snd i t

/-- Pullback invariance is equivalent to a commuting isomorphism between the target
and source pullbacks over the relation object. -/
theorem isPullbackInvariant_iff (s t : R ⟶ U) (i : T ⟶ U) :
    IsPullbackInvariant s t i ↔
      ∃ e : pullback i t ≅ pullback i s,
        e.hom ≫ pullback.snd i s = pullback.snd i t := sorry

end Morphism

namespace Subobject

/-- A subobject is invariant under parallel arrows when its pullbacks along the
target and source arrows are equal. -/
def IsInvariant (s t : R ⟶ U) (Q : Subobject U) : Prop :=
  (Subobject.pullback t).obj Q = (Subobject.pullback s).obj Q

/-- Subobject invariance is equivalent to equality of the target and source pullbacks. -/
theorem isInvariant_iff (s t : R ⟶ U) (Q : Subobject U) :
    IsInvariant s t Q ↔
      (Subobject.pullback t).obj Q = (Subobject.pullback s).obj Q := sorry

/-- A subobject represented by a monomorphism is invariant exactly when its two
pullbacks are isomorphic over the relation object. -/
theorem isInvariant_mk_iff (s t : R ⟶ U) (i : T ⟶ U) [Mono i] :
    IsInvariant s t (Subobject.mk i) ↔ Morphism.IsPullbackInvariant s t i := sorry

end Subobject
end CategoryTheory
