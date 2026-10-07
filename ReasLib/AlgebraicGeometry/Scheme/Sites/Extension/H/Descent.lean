module

public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Affine

/-!
# Directed-affine descent of h coverings

Finite affine h-covering families, their refinements, and equality of
refinements descend along directed inverse limits of affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.HCovering.Affine

noncomputable section

/-- A finite affine h-covering family of a directed affine limit descends to
an h-covering family at one of the affine stages. -/
theorem cover_exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD_affine : ∀ i : I, IsAffine (D.obj i)] [hlimit_affine : IsAffine c.pt]
    (family : AffineFamilyOver c.pt)
    [hfamily : Scheme.HCovering (fun j : Fin family.n ↦ Over.mk (family.map j))] :
    ∃ i : I, ∃ familyAt : AffineFamilyOver (D.obj i),
      Scheme.HCovering (fun j : Fin familyAt.n ↦ Over.mk (familyAt.map j)) ∧
        Nonempty (AffineFamilyOver.IsBaseChangeOf (c.π.app i) familyAt family) := sorry

namespace Refinement

/-- A refinement between the limit pullbacks of two finite affine h-covering
families descends after passing to a later stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
    {i : I} (sourceAt targetAt : AffineFamilyOver (D.obj i))
    [hsourceAt : Scheme.HCovering
      (fun j : Fin sourceAt.n ↦ Over.mk (sourceAt.map j))]
    [htargetAt : Scheme.HCovering
      (fun j : Fin targetAt.n ↦ Over.mk (targetAt.map j))]
    (limitRefinement : AffineFamilyOver.Refinement
      (sourceAt.pullback (T' := c.pt) (c.π.app i))
      (targetAt.pullback (T' := c.pt) (c.π.app i))) :
    ∃ i' : I, ∃ hi : i ≤ i',
      ∃ hsourceLimit :
        AffineFamilyOver.IsBaseChangeOf (c.π.app i')
          (sourceAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
          (sourceAt.pullback (T' := c.pt) (c.π.app i)),
      ∃ htargetLimit :
        AffineFamilyOver.IsBaseChangeOf (c.π.app i')
          (targetAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
          (targetAt.pullback (T' := c.pt) (c.π.app i)),
      ∃ refinement : AffineFamilyOver.Refinement
          (sourceAt.pullback (T' := D.obj i') (D.map (homOfLE hi)))
          (targetAt.pullback (T' := D.obj i') (D.map (homOfLE hi))),
        Nonempty (AffineFamilyOver.Refinement.IsBaseChangeOf
          hsourceLimit htargetLimit refinement limitRefinement) := sorry

/-- Two refinements of finite affine h-covering families which agree after
pullback to a directed affine limit agree at some later stage. -/
theorem eventually_equal
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
    {i : I} (sourceAt targetAt : AffineFamilyOver (D.obj i))
    [hsourceAt : Scheme.HCovering
      (fun j : Fin sourceAt.n ↦ Over.mk (sourceAt.map j))]
    [htargetAt : Scheme.HCovering
      (fun j : Fin targetAt.n ↦ Over.mk (targetAt.map j))]
    (firstAt secondAt : AffineFamilyOver.Refinement sourceAt targetAt)
    (heq : firstAt.pullback (T' := c.pt) (c.π.app i) =
      secondAt.pullback (T' := c.pt) (c.π.app i)) :
    ∃ i' : I, ∃ hi : i ≤ i',
      firstAt.pullback (T' := D.obj i') (D.map (homOfLE hi)) =
        secondAt.pullback (T' := D.obj i') (D.map (homOfLE hi)) := sorry

end Refinement

end

end AlgebraicGeometry.Scheme.HCovering.Affine
