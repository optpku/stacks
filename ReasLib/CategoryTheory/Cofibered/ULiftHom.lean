module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Hom-universe lifts of cofibered projections

Hom-universe lifting preserves the property of being cofibered in groupoids.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

/-- The Hom-universe lift of a projection cofibered in groupoids is cofibered in groupoids. -/
instance uliftHomProjection_op_inGroupoids
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (p : D ⥤ C) [Functor.IsFibered.InGroupoids p.op] :
    Functor.IsFibered.InGroupoids
      (ULiftHom.down ⋙ p : ULiftHom.{w} D ⥤ C).op := sorry

end CategoryTheory.Functor
