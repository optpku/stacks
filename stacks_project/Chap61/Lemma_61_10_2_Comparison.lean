/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

/-!
# Standard V coverings as directed affine ph/h limits

This leaf compares singleton standard `V` coverings of affine schemes with
directed inverse-limit presentations by affine singleton `ph` and `h`
coverings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace AffineFamilyOver

/-- The singleton family associated to a scheme morphism is a `ph` covering. -/
def IsSingletonPhCover {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  PhCovering (fun _ : Unit ↦ X) (fun _ : Unit ↦ f)

/-- A morphism is a singleton `ph` covering exactly when the corresponding
singleton family is a `ph` covering. -/
theorem isSingletonPhCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSingletonPhCover f ↔
      PhCovering (fun _ : Unit ↦ X) (fun _ : Unit ↦ f) :=
    sorry

/-- The singleton family associated to a scheme morphism is an `h` covering. -/
def IsSingletonHCover {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Scheme.HCovering (fun _ : Unit ↦ Over.mk f)

/-- A morphism is a singleton `h` covering exactly when the corresponding
singleton family is an `h` covering. -/
theorem isSingletonHCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSingletonHCover f ↔
      Scheme.HCovering (fun _ : Unit ↦ Over.mk f) :=
    sorry

/-- An affine morphism over an affine base is a directed inverse limit of
affine schemes over that base whose stage morphisms are singleton `ph`
coverings. -/
def IsDirectedPhCover {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : Prop :=
  ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
    (D : OrderDual I ⥤ Scheme.{u}) (_ : ∀ i, IsAffine (D.obj i))
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D),
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        π ≫ t = (Functor.const _).map f ∧
          ∀ i, IsSingletonPhCover (t.app i)

/-- An affine morphism over an affine base is a directed inverse limit of
affine schemes over that base whose stage morphisms are singleton `h`
coverings. -/
def IsDirectedHCover {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : Prop :=
  ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
    (D : OrderDual I ⥤ Scheme.{u}) (_ : ∀ i, IsAffine (D.obj i))
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D),
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        π ≫ t = (Functor.const _).map f ∧
          ∀ i, IsSingletonHCover (t.app i)

/-- A directed inverse-limit presentation by affine singleton `ph` coverings
is exactly the data of such a directed affine system with apex the source. -/
theorem isDirectedPhCover_iff {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    IsDirectedPhCover f ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ Scheme.{u}) (_ : ∀ i, IsAffine (D.obj i))
        (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
        (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
            π ≫ t = (Functor.const _).map f ∧
              ∀ i, IsSingletonPhCover (t.app i) :=
    sorry

/-- A directed inverse-limit presentation by affine singleton `h` coverings
is exactly the data of such a directed affine system with apex the source. -/
theorem isDirectedHCover_iff {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    IsDirectedHCover f ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ Scheme.{u}) (_ : ∀ i, IsAffine (D.obj i))
        (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
        (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
            π ≫ t = (Functor.const _).map f ∧
              ∀ i, IsSingletonHCover (t.app i) :=
    sorry

/-- For a morphism of affine schemes, being a singleton standard `V` covering
is equivalent to being a directed inverse limit of affine singleton `ph`
coverings over the base, and to the same with singleton `h` coverings. -/
theorem isStandardVCover_singleton_tfae
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE [IsStandardVCover (singleton f inferInstance),
      IsDirectedPhCover f, IsDirectedHCover f] :=
    sorry

/-- A morphism of affine schemes is a singleton standard `V` covering if and
only if it is a directed inverse limit of affine singleton `ph` coverings. -/
theorem isStandardVCover_iff_isDirectedPhCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    IsStandardVCover (singleton f inferInstance) ↔ IsDirectedPhCover f :=
    sorry

/-- A morphism of affine schemes is a singleton standard `V` covering if and
only if it is a directed inverse limit of affine singleton `h` coverings. -/
theorem isStandardVCover_iff_isDirectedHCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    IsStandardVCover (singleton f inferInstance) ↔ IsDirectedHCover f :=
    sorry

/-- Directed inverse-limit presentations by affine singleton `ph` coverings
and by affine singleton `h` coverings are equivalent. -/
theorem isDirectedPhCover_iff_isDirectedHCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    IsDirectedPhCover f ↔ IsDirectedHCover f :=
    sorry

/-- A singleton standard `V` covering of affine schemes admits a directed
inverse-limit presentation by affine singleton `ph` coverings. -/
theorem exists_isDirectedPhCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : IsStandardVCover (singleton f inferInstance)) :
    IsDirectedPhCover f :=
    sorry

/-- A singleton standard `V` covering of affine schemes admits a directed
inverse-limit presentation by affine singleton `h` coverings. -/
theorem exists_isDirectedHCover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : IsStandardVCover (singleton f inferInstance)) :
    IsDirectedHCover f :=
    sorry

/-- If a directed inverse system of affine schemes over an affine base has
singleton `ph` covering stages, then the limit-to-base morphism is a
singleton standard `V` covering. -/
theorem isStandardVCover_of_forall_stage_phCovering
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {Y : Scheme.{u}} [IsAffine Y]
    (D : OrderDual I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) [IsAffine c.pt]
    (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    (h : ∀ i, IsSingletonPhCover (t.app i)) :
    IsStandardVCover (singleton σlim inferInstance) :=
    sorry

end AffineFamilyOver
end AlgebraicGeometry
