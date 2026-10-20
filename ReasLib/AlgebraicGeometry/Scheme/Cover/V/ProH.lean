module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

/-!
# Standard V coverings as directed affine ph/h limits

Singleton standard `V` coverings of affine schemes are compared with directed
inverse-limit presentations by affine singleton `ph` and `h` coverings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace AffineFamilyOver

/-- A morphism between affine schemes admits a directed inverse-limit
presentation over its target by affine schemes whose stage morphisms are
singleton `ph` coverings. -/
def IsDirectedPhCover {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : Prop :=
  ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
    (D : OrderDual I ⥤ Scheme.{u}) (_ : ∀ i, IsAffine (D.obj i))
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D),
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        π ≫ t = (Functor.const _).map f ∧
          ∀ i, PhCovering (fun _ : Unit ↦ D.obj i) (fun _ : Unit ↦ t.app i)

/-- A morphism between affine schemes admits a directed inverse-limit
presentation over its target by affine schemes whose stage morphisms are
singleton `h` coverings. -/
def IsDirectedHCover {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : Prop :=
  ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
    (D : OrderDual I ⥤ Scheme.{u}) (_ : ∀ i, IsAffine (D.obj i))
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D),
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        π ≫ t = (Functor.const _).map f ∧
          ∀ i, Scheme.HCovering (fun _ : Unit ↦ Over.mk (t.app i))

/-- For a morphism between affine schemes, being a singleton standard `V`
covering is equivalent to being a directed inverse limit of affine singleton
`ph` coverings over the base, and to the same with singleton `h` coverings. -/
theorem isStandardVCover_singleton_tfae
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE [IsStandardVCover (singleton f inferInstance),
      IsDirectedPhCover f, IsDirectedHCover f] := sorry

/-- A morphism between affine schemes is a singleton standard `V` covering if
and only if it is a directed inverse limit of affine singleton `ph` coverings. -/
theorem isStandardVCover_iff_isDirectedPhCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    IsStandardVCover (singleton f inferInstance) ↔ IsDirectedPhCover f := sorry

/-- A morphism between affine schemes is a singleton standard `V` covering if
and only if it is a directed inverse limit of affine singleton `h` coverings. -/
theorem isStandardVCover_iff_isDirectedHCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    IsStandardVCover (singleton f inferInstance) ↔ IsDirectedHCover f := sorry

end AffineFamilyOver
end AlgebraicGeometry
