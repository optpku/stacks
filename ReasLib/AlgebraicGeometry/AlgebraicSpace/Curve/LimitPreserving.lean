module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.CategoryTheory.Fibered.Fiber.DirectedSystem
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Limit preservation for families of curves

Families of curves descend along directed affine inverse limits, and the
canonical fibre Hom-cocones are colimit cocones.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Functor.Fiber

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Object descent for `p S` along directed inverse limits of affine schemes
over `S`. -/
theorem exists_stage (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : (p S).Fiber c.pt) :
    ∃ (i : I) (xi : (p S).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x :=
  sorry

/-- Fibre Hom-types of `p S` over a directed inverse limit of affine schemes
over `S` are the directed colimit of the corresponding stage Hom-types. -/
theorem hom_isColimit (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : (p S).Fiber (D.obj i)) :
    Nonempty (IsColimit (DirectedSystem.homCocone (p S) c x y)) :=
  sorry

/-- Families of curves form a limit-preserving category fibred in groupoids:
objects descend up to isomorphism along directed affine inverse limits, and the
canonical fibre Hom-cocones are colimit cocones. -/
@[stacks 0D55]
theorem isLimitPreserving (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : (p S).Fiber c.pt,
      ∃ (i : I) (xi : (p S).Fiber (D.obj i)),
        IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (p S).Fiber (D.obj i)),
        Nonempty (IsColimit (DirectedSystem.homCocone (p S) c x y)) :=
  ⟨exists_stage S D c hc hD hpt, hom_isColimit S D c hc hD hpt⟩

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
