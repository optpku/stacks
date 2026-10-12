/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard.BaseChange

/-!
# Directed-affine descent of standard covers

This leaf owns descent and eventual-equality statements for finite affine
standard covers. It is independent of the Grothendieck topology and
presheaf-extension machinery.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

namespace StandardTopology
namespace Affine

/-- A finite affine standard cover of a directed affine limit descends to one
of the stages. -/
theorem cover_exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (hD_affine : ∀ i : I, IsAffine (D.obj i))
    (τ : StandardTopology) (family : AffineFamilyOver c.pt)
    (hfamily : τ.IsCover family) :
    ∃ i : I, ∃ familyAt : AffineFamilyOver (D.obj i),
      τ.IsCover familyAt ∧
        Nonempty (AffineFamilyOver.IsBaseChangeOf (c.π.app i) familyAt family) := sorry

namespace Refinement

/-- A refinement of base-changed standard covers descends after passing to a
later stage of a directed affine limit. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
    (τ : StandardTopology) {i : I}
    (sourceAt targetAt : AffineFamilyOver (D.obj i))
    (hsourceAt : τ.IsCover sourceAt) (htargetAt : τ.IsCover targetAt)
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

/-- Refinements of standard covers which agree after base change to a directed
affine limit agree after passing to a later stage. -/
theorem eventually_equal
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [hD_affine : ∀ k : I, IsAffine (D.obj k)] [hlimit_affine : IsAffine c.pt]
    (τ : StandardTopology) {i : I}
    (sourceAt targetAt : AffineFamilyOver (D.obj i))
    (hsourceAt : τ.IsCover sourceAt) (htargetAt : τ.IsCover targetAt)
    (firstAt secondAt : AffineFamilyOver.Refinement sourceAt targetAt)
    (heq : firstAt.pullback (T' := c.pt) (c.π.app i) =
      secondAt.pullback (T' := c.pt) (c.π.app i)) :
    ∃ i' : I, ∃ hi : i ≤ i',
      firstAt.pullback (T' := D.obj i') (D.map (homOfLE hi)) =
        secondAt.pullback (T' := D.obj i') (D.map (homOfLE hi)) := sorry

end Refinement
end Affine
end StandardTopology

end

end AlgebraicGeometry
