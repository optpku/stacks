/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Equivalence

/-!
# Explicit quasi-inverses of functors

`Functor.IsEquivalence` is the canonical proposition-level owner. `Functor.QuasiInverse` packages
the explicit inverse functor and the two comparison isomorphisms when later constructions need
to refer to that data.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]

/-- A pair of functors are quasi-inverse when they are isomorphic to the respective identities. -/
@[stacks 001J "quasi-inverse functors"]
def IsQuasiInverse (F : A ⥤ B) (G : B ⥤ A) : Prop :=
  Nonempty (𝟭 A ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 B)

namespace IsQuasiInverse

variable {F : A ⥤ B} {G : B ⥤ A}

/-- Quasi-inverse functors remain quasi-inverse after exchanging their roles. -/
theorem symm (h : F.IsQuasiInverse G) : G.IsQuasiInverse F := by
  rcases h with ⟨⟨η⟩, ⟨ε⟩⟩
  exact ⟨⟨ε.symm⟩, ⟨η.symm⟩⟩

/-- A functor with a quasi-inverse is an equivalence of categories. -/
theorem isEquivalence (h : F.IsQuasiInverse G) : F.IsEquivalence := by
  rcases h with ⟨⟨η⟩, ⟨ε⟩⟩
  exact IsEquivalence.mk' G η ε

end IsQuasiInverse

/-- Explicit quasi-inverse data for a functor. -/
@[stacks 001J "explicit quasi-inverse data"]
structure QuasiInverse (F : A ⥤ B) where
  /-- The inverse functor. -/
  inverse : B ⥤ A
  /-- The unit comparison with the identity on the source. -/
  unitIso : 𝟭 A ≅ F ⋙ inverse
  /-- The counit comparison with the identity on the target. -/
  counitIso : inverse ⋙ F ≅ 𝟭 B

namespace QuasiInverse

variable {F : A ⥤ B}

/-- Forget the triangle identity of an equivalence of categories while retaining its forward
functor, inverse, unit, and counit as explicit quasi-inverse data. -/
def ofEquivalence (e : A ≌ B) : QuasiInverse e.functor where
  inverse := e.inverse
  unitIso := e.unitIso
  counitIso := e.counitIso

/-- The inverse stored after forgetting an equivalence's triangle identity is its original
inverse functor. -/
@[simp]
theorem ofEquivalence.inverse (e : A ≌ B) :
    (ofEquivalence e).inverse = e.inverse := rfl

/-- Forgetting an equivalence's triangle identity retains its unit isomorphism. -/
@[simp]
theorem ofEquivalence.unitIso (e : A ≌ B) :
    (ofEquivalence e).unitIso = e.unitIso := rfl

/-- Forgetting an equivalence's triangle identity retains its counit isomorphism. -/
@[simp]
theorem ofEquivalence.counitIso (e : A ≌ B) :
    (ofEquivalence e).counitIso = e.counitIso := rfl

/-- Reverse quasi-inverse data by exchanging the forward and inverse functors. -/
def symm (e : QuasiInverse F) : QuasiInverse e.inverse where
  inverse := F
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm

/-- Reversing explicit quasi-inverse data selects the original forward functor as its inverse. -/
@[simp]
theorem symm.inverse (e : QuasiInverse F) :
    e.symm.inverse = F := rfl

/-- Reversing explicit quasi-inverse data uses the inverse counit as its unit. -/
@[simp]
theorem symm.unitIso (e : QuasiInverse F) :
    e.symm.unitIso = e.counitIso.symm := rfl

/-- Reversing explicit quasi-inverse data uses the inverse unit as its counit. -/
@[simp]
theorem symm.counitIso (e : QuasiInverse F) :
    e.symm.counitIso = e.unitIso.symm := rfl

/-- Explicit quasi-inverse data imply that the forward functor is an equivalence. -/
theorem isEquivalence (e : QuasiInverse F) : F.IsEquivalence :=
  IsEquivalence.mk' e.inverse e.unitIso e.counitIso

end QuasiInverse

end CategoryTheory.Functor
