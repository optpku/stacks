module

public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback.Basic

/-!
# Stability consequences for strongly cartesian pullbacks

This file owns closure under chosen pullbacks, reflection of strongly cartesian first
projections, and preservation of the corresponding pullback squares in the base.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsStronglyCartesian

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]
variable (p : E ⥤ C)

/-- If both original legs are strongly cartesian, then the named first projection of the canonical
chosen-pullback square is strongly cartesian. -/
@[stacks 06N5 "canonical pullback first projection is strongly cartesian"]
theorem Pullback.fst.isStronglyCartesian
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian (p.map ψ) ψ] :
    p.IsStronglyCartesian (pullback.fst (p.map φ) (p.map ψ))
      (Pullback.fst p φ ψ) := sorry

/-- A strongly cartesian morphism admits pullbacks along every
morphism whose image admits the corresponding pullback in the base. -/
@[stacks 06NU "pullback existence along a strongly cartesian morphism"]
theorem hasPullback
    [p.IsFibered] {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    HasPullback φ ψ := sorry

/-- In a pullback square whose right leg is strongly cartesian, the
first pullback projection is strongly cartesian. -/
@[stacks 06NU "strong cartesianness of a pullback projection"]
theorem fst_of_isPullback
    [p.IsFibered] {x y z w : E} {φ : x ⟶ y} {g : z ⟶ y}
    {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ) :
    p.IsStronglyCartesian (p.map χ) χ := sorry

/-- Mapping a pullback square along a fibred functor yields a
pullback square in the base when its right leg is strongly cartesian. -/
@[stacks 06NU "reflection of pullback squares along a fibred projection"]
theorem map_isPullback
    [p.IsFibered] {x y z w : E} {φ : x ⟶ y} {g : z ⟶ y}
    {χ : w ⟶ z} {a : w ⟶ x}
    (hφ : p.IsStronglyCartesian (p.map φ) φ)
    (h : IsPullback χ a g φ) :
    IsPullback (p.map χ) (p.map a) (p.map g) (p.map φ) := sorry

end CategoryTheory.Functor.IsStronglyCartesian
