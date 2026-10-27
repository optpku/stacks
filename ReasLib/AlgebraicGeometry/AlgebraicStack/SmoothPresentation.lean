/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Smooth presentations of morphisms of algebraic stacks

Presentation squares have smooth vertical morphisms and a surjective source atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A commutative square presenting a morphism of algebraic stacks by algebraic
spaces, with smooth vertical arrows, surjective source atlas, and a 2-isomorphic
comparison of the two paths `U.toGroupoids ⟶ Y`. -/
def IsSmoothSurjectivePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Surjective a ∧
    Groupoids.Hom.Smooth b ∧
      Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)

/-- Unfolding of a smooth surjective algebraic-space presentation square. -/
theorem isSmoothSurjectivePresentation_iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsSmoothSurjectivePresentation f a b h ↔
      Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Surjective a ∧
        Groupoids.Hom.Smooth b ∧
          Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  Iff.rfl

/-- A 2-commutative square presenting a morphism of algebraic stacks by algebraic
spaces, with smooth vertical arrows. -/
def IsSmoothSpaceSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Smooth b ∧
    Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)

/-- A square is a smooth algebraic-space presentation square if and only if the
vertical arrows are smooth and the two paths `U.toGroupoids ⟶ Y` are
2-isomorphic. -/
theorem IsSmoothSpaceSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsSmoothSpaceSquare f a b h ↔
      Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Smooth b ∧
        Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  Iff.rfl

/-- Smooth vertical arrows and a 2-isomorphism of paths yield a smooth
algebraic-space presentation square. -/
theorem IsSmoothSpaceSquare.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (ha : Groupoids.Hom.Smooth a)
    (hb : Groupoids.Hom.Smooth b)
    (hsq : Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)) :
    IsSmoothSpaceSquare f a b h :=
  ⟨ha, hb, hsq⟩

/-- A smooth algebraic-space presentation square has smooth vertical arrows and
a 2-isomorphism of the two paths `U.toGroupoids ⟶ Y`. -/
theorem IsSmoothSpaceSquare.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hsq : IsSmoothSpaceSquare f a b h) :
    Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Smooth b ∧
      Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  hsq

/-- The comparison `U ⟶ X ×_Y V` is smooth: some 1-morphism to the chosen
2-fibre product `TwoFibreProduct.apex f b` is smooth and 2-isomorphic to the
given legs `a` and `toGroupoids.map h`. -/
def HasSmoothComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
    Groupoids.Hom.Smooth φ ∧
      Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
        Nonempty
          (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
            AlgebraicSpace.toGroupoids.map h)

/-- Smooth comparison into `TwoFibreProduct.apex f b` means some smooth 1-morphism
is 2-isomorphic to the given legs. -/
theorem HasSmoothComparison.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    HasSmoothComparison f a b h ↔
      ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
        Groupoids.Hom.Smooth φ ∧
          Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
            Nonempty
              (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
                AlgebraicSpace.toGroupoids.map h) :=
  Iff.rfl

/-- A smooth comparison 1-morphism into `TwoFibreProduct.apex f b` witnesses
`HasSmoothComparison`. -/
theorem HasSmoothComparison.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b)
    (hφ : Groupoids.Hom.Smooth φ)
    (hfst : Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a))
    (hsnd : Nonempty
      (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
        AlgebraicSpace.toGroupoids.map h)) :
    HasSmoothComparison f a b h :=
  ⟨φ, hφ, hfst, hsnd⟩

/-- A smooth comparison supplies a 1-morphism `φ` to `TwoFibreProduct.apex f b`
that is smooth and 2-isomorphic to the given legs. -/
theorem HasSmoothComparison.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hφ : HasSmoothComparison f a b h) :
    ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
      Groupoids.Hom.Smooth φ ∧
        Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
          Nonempty
            (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
              AlgebraicSpace.toGroupoids.map h) :=
  hφ

/-- A square is a smooth surjective presentation if and only if it is a smooth
algebraic-space square whose source atlas is surjective. -/
theorem IsSmoothSurjectivePresentation.iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsSmoothSurjectivePresentation f a b h ↔
      IsSmoothSpaceSquare f a b h ∧ Groupoids.Hom.Surjective a :=
  ⟨fun ⟨ha, hsurj, hb, hsq⟩ ↦ ⟨⟨ha, hb, hsq⟩, hsurj⟩,
    fun ⟨⟨ha, hb, hsq⟩, hsurj⟩ ↦ ⟨ha, hsurj, hb, hsq⟩⟩

/-- A smooth algebraic-space square with surjective source atlas is a smooth
surjective presentation. -/
theorem IsSmoothSurjectivePresentation.of {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hsq : IsSmoothSpaceSquare f a b h) (ha : Groupoids.Hom.Surjective a) :
    IsSmoothSurjectivePresentation f a b h :=
  (IsSmoothSurjectivePresentation.iff f a b h).mpr ⟨hsq, ha⟩

/-- A smooth surjective presentation is a smooth algebraic-space square with
surjective source atlas. -/
theorem IsSmoothSurjectivePresentation.spec {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hpres : IsSmoothSurjectivePresentation f a b h) :
    IsSmoothSpaceSquare f a b h ∧ Groupoids.Hom.Surjective a :=
  (IsSmoothSurjectivePresentation.iff f a b h).mp hpres

end AlgebraicGeometry.AlgebraicStack
