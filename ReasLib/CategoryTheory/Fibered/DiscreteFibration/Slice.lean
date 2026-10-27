/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The slice projection as a discrete fibration

Precomposition gives the canonical unique lift through `Over.forget X`. This file keeps that
explicit construction and the resulting reusable instance independent of representable
presheaves.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Over.ForgetLift

variable {X R : C} (a : Over X) (f : R ⟶ a.left)

/-- The canonical domain of the lift of `f : R ⟶ a.left` through the slice projection:
the composite arrow `R ⟶ X`. -/
@[stacks 0043 "canonical domain for a slice-projection lift"]
def domain : Over X :=
  Over.mk (f ≫ a.hom)

/-- The canonical slice morphism from the precomposition object to `a`, with underlying arrow
`f`. -/
@[stacks 0043 "canonical morphism for a slice-projection lift"]
def hom : domain a f ⟶ a :=
  Over.homMk f

/-- The underlying object of the canonical lift domain is the source of the base arrow. -/
@[simp]
theorem domain.left : (domain a f).left = R := sorry

/-- The structure arrow of the canonical lift domain is precomposition by the base arrow. -/
@[simp]
theorem domain.hom : (domain a f).hom = f ≫ a.hom := sorry

/-- The underlying arrow of the canonical slice lift is the displayed base arrow. -/
@[simp]
theorem hom.left : (hom a f).left = f := sorry

/-- The canonical slice morphism lifts the displayed base arrow through `Over.forget X`. -/
theorem hom.isHomLift :
    (Over.forget X).IsHomLift f (hom a f) := sorry

/-- The complete canonical lift of `f` through the slice projection.

Its object and morphism fields are explicit; the lifting certificate uses mathlib's canonical
`IsHomLift.map`, so the non-`Prop` payload does not depend on an existential choice or `sorryAx`. -/
@[stacks 0043 "canonical lift for the slice projection"]
def lift : Functor.HomLift (Over.forget X) f where
  domain := domain a f
  hom := hom a f
  isHomLift := Functor.IsHomLift.map (hom a f)

/-- The domain field of the complete canonical lift is the precomposition object. -/
@[simp]
theorem lift.domain : (lift a f).domain = domain a f := sorry

/-- The morphism field of the complete canonical lift is the canonical slice morphism. -/
@[simp]
theorem lift.hom : (lift a f).hom = hom a f := sorry

/-- Every lift of `f` through the slice projection is the canonical precomposition lift. -/
theorem unique (l : Functor.HomLift (Over.forget X) f) :
    l = lift a f := sorry

/-- Lifts of a fixed arrow with fixed codomain through the slice projection are subsingletons. -/
theorem subsingleton : Subsingleton (Functor.HomLift (Over.forget X) f) := sorry

end Over.ForgetLift

/-- The canonical slice projection is a discrete fibration: every arrow into `X` has a unique
cartesian lift obtained by precomposition. This reusable instance belongs with the intrinsic
`Functor.IsDiscreteFibration` owner rather than with any particular representable-presheaf example.

Proof strategy: lift `f : Z ⟶ Y` at `Y ⟶ X` by the triangle `Z ⟶ Y ⟶ X`; uniqueness follows
from `Over.ext` and the commuting-triangle law. -/
@[stacks 0043 "the slice projection is a discrete fibration"]
instance Over.forgetIsDiscreteFibration (X : C) :
    Functor.IsDiscreteFibration (Over.forget X) where
  homLiftNonempty f := ⟨Over.ForgetLift.lift _ f⟩
  homLiftSubsingleton f := Over.ForgetLift.subsingleton _ f

/-- The canonical arrow from a slice object to the terminal identity object is strongly
Cartesian over the object's structure arrow. -/
@[stacks 0043 "the terminal slice arrow is strongly Cartesian"]
theorem Over.mkIdTerminal.from.isStronglyCartesian {X : C} (a : Over X) :
    (Over.forget X).IsStronglyCartesian a.hom (Over.mkIdTerminal.from a) := by
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · apply IsHomLift.of_fac (Over.forget X) a.hom
      (Over.mkIdTerminal.from a) rfl rfl
    change a.hom = 𝟙 a.left ≫ (Over.mkIdTerminal.from a).left ≫ 𝟙 X
    simp only [Over.mkIdTerminal_from_left, Category.id_comp]
    exact (Category.comp_id a.hom).symm
  · intro b g phi hphi
    letI := hphi
    have hmap : g ≫ a.hom = phi.left := by
      have h := IsHomLift.fac (Over.forget X) (g ≫ a.hom) phi
      change g ≫ a.hom = 𝟙 b.left ≫ phi.left ≫ 𝟙 X at h
      exact h.trans ((Category.id_comp _).trans (Category.comp_id phi.left))
    have htri : phi.left = b.hom := by
      have h := Over.w phi
      change phi.left ≫ 𝟙 X = b.hom at h
      exact (Category.comp_id phi.left).symm.trans h
    let psi : b ⟶ a := Over.homMk g (hmap.trans htri)
    refine ⟨psi, ⟨?_, ?_⟩, ?_⟩
    · apply IsHomLift.of_fac (Over.forget X) g psi rfl rfl
      change g = 𝟙 b.left ≫ g ≫ 𝟙 a.left
      simp only [Category.id_comp, Category.comp_id]
    · exact Over.mkIdTerminal.hom_ext _ _
    · intro psi' hpsi'
      letI := hpsi'.1
      have h := IsHomLift.fac' (Over.forget X) g psi'
      change psi'.left = 𝟙 b.left ≫ g ≫ 𝟙 a.left at h
      apply Over.OverMorphism.ext
      change psi'.left = g
      simpa only [Category.id_comp, Category.comp_id] using h

end CategoryTheory
