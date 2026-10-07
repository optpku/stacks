module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Zariski covering families of algebraic spaces

This module establishes the basic stability laws of Zariski covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/-- A singleton family induced by an isomorphism is a Zariski covering. -/
theorem isZariskiCover_of_isIso {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) [IsIso f] :
    IsZariskiCover X (fun _ : PUnit.{u + 1} ↦ X') (fun _ ↦ f) :=
  sorry

/-- The composite of a Zariski covering with Zariski coverings of its members is a Zariski
covering. -/
theorem isZariskiCover_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type v} [Small.{u} I] {Xᵢ : I → AlgebraicSpace S}
    (f : ∀ i, Xᵢ i ⟶ X) (hf : IsZariskiCover X Xᵢ f)
    {J : I → Type w} [∀ i, Small.{u} (J i)]
    {Xᵢⱼ : ∀ i, J i → AlgebraicSpace S}
    (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
    (hg : ∀ i, IsZariskiCover (Xᵢ i) (Xᵢⱼ i) (g i)) :
    IsZariskiCover X (fun p : Sigma J ↦ Xᵢⱼ p.1 p.2)
      (fun p ↦ g p.1 p.2 ≫ f p.1) :=
  sorry

/-- Pulling back a Zariski covering along a morphism of algebraic spaces gives a Zariski covering. -/
theorem isZariskiCover_pullback {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {I : Type v} [Small.{u} I] {Xᵢ : I → AlgebraicSpace S}
    (f : ∀ i, Xᵢ i ⟶ X) (hf : IsZariskiCover X Xᵢ f) (h : X' ⟶ X) :
    IsZariskiCover X' (fun i ↦ pullback h (f i))
      (fun i ↦ pullback.fst h (f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
