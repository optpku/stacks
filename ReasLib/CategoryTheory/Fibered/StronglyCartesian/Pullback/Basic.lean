/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Chosen
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback squares from strongly cartesian morphisms

This file owns the general square criterion and the canonical first projection of the lifted
pullback square.  The cone and stability consequences are layered separately.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open IsStronglyCartesian IsHomLift IsPreFibered

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

variable (p : E ⥤ C) {x y z w : E} (φ : x ⟶ y) (ψ : z ⟶ y)

namespace IsStronglyCartesian

/-- A pullback square in the base lifts to a pullback square in the total category when its two
relevant lifted legs are strongly cartesian. The lift `χ` is arbitrary, provided it lies over
the corresponding base arrow and the lifted square commutes. -/
@[stacks 06N4]
theorem isPullback_of_base
    {R : C} {f : R ⟶ p.obj x} {g : R ⟶ p.obj z}
    {χ : w ⟶ x} (hbase : IsPullback f g (p.map φ) (p.map ψ))
    (a : w ⟶ z) [p.IsHomLift f χ]
    [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian g a] (hχ : χ ≫ φ = a ≫ ψ) :
    IsPullback χ a φ ψ := sorry

/-- Canonical-lift form of `isPullback_of_base`: the first leg is selected by the strongly
cartesian lifting property, so ordinary chosen-pullback clients need no separate lift witness. -/
@[stacks 06N4 "canonical strongly-cartesian lift"]
theorem isPullback_of_base_map
    {R : C} {f : R ⟶ p.obj x} {g : R ⟶ p.obj z}
    (hbase : IsPullback f g (p.map φ) (p.map ψ))
    (a : w ⟶ z)
    [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian g a] :
    IsPullback
      (IsStronglyCartesian.map p (p.map φ) φ hbase.w.symm (a ≫ ψ))
      a φ ψ := sorry

/-- If `φ` and `a` are strongly cartesian over the first map and second projection of the chosen
base pullback, then their induced square is a pullback square in the total category. -/
@[stacks 06N5 "pullback square from chosen strongly-cartesian legs"]
theorem isPullback_of_hasPullback
    {a : w ⟶ z} [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian (pullback.snd (p.map φ) (p.map ψ)) a] :
    IsPullback
      (IsStronglyCartesian.map p (p.map φ) φ
        (IsPullback.of_hasPullback (p.map φ) (p.map ψ)).w.symm
        (a ≫ ψ))
      a φ ψ := sorry

namespace Pullback

/-- The first projection of the canonical total-category pullback candidate.  The apex and
second projection are mathlib's chosen `IsPreFibered.pullbackObj` and
`IsPreFibered.pullbackMap`; this definition names only the genuinely new arrow obtained from the
strongly cartesian universal property of `φ`. -/
@[stacks 06N5 "canonical pullback first projection"]
noncomputable def fst
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    IsPreFibered.pullbackObj (p := p) rfl
        (pullback.snd (p.map φ) (p.map ψ)) ⟶ x :=
  IsStronglyCartesian.map p (p.map φ) φ
    (IsPullback.of_hasPullback (p.map φ) (p.map ψ)).w.symm
    (IsPreFibered.pullbackMap (p := p) rfl
      (pullback.snd (p.map φ) (p.map ψ)) ≫ ψ)

/-- The canonical first projection lifts the first projection of the chosen base pullback. -/
@[stacks 06N5 "canonical pullback first projection lift"]
theorem fst.isHomLift
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    p.IsHomLift (pullback.fst (p.map φ) (p.map ψ)) (fst p φ ψ) := sorry

/-- The first and second maps of the canonical chosen-pullback square commute. -/
@[reassoc (attr := simp), stacks 06N5 "canonical pullback projection compatibility"]
theorem fst_comp
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    fst p φ ψ ≫ φ =
      IsPreFibered.pullbackMap (p := p) rfl
        (pullback.snd (p.map φ) (p.map ψ)) ≫ ψ := sorry

/-- The canonical first leg together with mathlib's chosen second lift forms a pullback square. -/
@[stacks 06N5]
theorem isPullback
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    IsPullback (fst p φ ψ)
      (IsPreFibered.pullbackMap (p := p) rfl
        (pullback.snd (p.map φ) (p.map ψ))) φ ψ := sorry

end Pullback
end IsStronglyCartesian
end CategoryTheory.Functor
