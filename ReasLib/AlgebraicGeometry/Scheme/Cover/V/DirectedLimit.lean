/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

/-!
# Standard V coverings along directed affine limits

Singleton standard `V` coverings of a directed inverse limit of affine schemes
over an affine base are equivalent to standard `V` coverings at every stage.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace AffineFamilyOver

/-- Over an affine scheme, the singleton family of a directed inverse-limit
morphism is a standard `V` covering if and only if every stage morphism, as a
singleton family, is a standard `V` covering. -/
theorem isStandardVCover_limitHom_iff
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {Y : Scheme.{u}} [IsAffine Y]
    (D : OrderDual I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c)
    (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim) :
    IsStandardVCover (singleton σlim (Scheme.isAffine_of_isLimit c hc)) ↔
      ∀ i, IsStandardVCover (singleton (t.app i) inferInstance) := sorry

namespace IsStandardVCover

/-- If the limit-to-base morphism is a singleton standard `V` covering, then
every stage-to-base morphism is a singleton standard `V` covering. -/
theorem of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {Y : Scheme.{u}} [IsAffine Y]
    (D : OrderDual I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c)
    (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    (h : IsStandardVCover (singleton σlim (Scheme.isAffine_of_isLimit c hc))) :
    ∀ i, IsStandardVCover (singleton (t.app i) inferInstance) := sorry

/-- If every stage-to-base morphism is a singleton standard `V` covering, then
the limit-to-base morphism is a singleton standard `V` covering. -/
theorem of_forall_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {Y : Scheme.{u}} [IsAffine Y]
    (D : OrderDual I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c)
    (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    (h : ∀ i, IsStandardVCover (singleton (t.app i) inferInstance)) :
    IsStandardVCover (singleton σlim (Scheme.isAffine_of_isLimit c hc)) := sorry

end IsStandardVCover

end AffineFamilyOver
end AlgebraicGeometry
