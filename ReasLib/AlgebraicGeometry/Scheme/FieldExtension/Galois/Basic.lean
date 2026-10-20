module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Equivariance

/-!
# Galois automorphisms of field-extension base changes

This leaf specializes the equivariance API to `Gal(K / k)`.  The induced
scheme automorphism is exposed separately from any action on a chosen
topological invariant.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois

/-- The automorphism of `Spec K` induced by a `k`-automorphism of `K`. -/
noncomputable abbrev baseAut
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)

/-- A Galois automorphism of `Spec K` lies over `Spec k`. -/
theorem baseAut_over
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) :
    baseAut k K σ ≫ FieldExtension.specMap k K =
      FieldExtension.specMap k K := by
  dsimp [baseAut, FieldExtension.specMap, Scheme.AffineBaseChange.specMap]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- The endomorphism of a field-extension base change induced by a Galois element. -/
noncomputable abbrev map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    FieldExtension.baseChange k K f ⟶ FieldExtension.baseChange k K f :=
  FieldExtension.Equivariance.map f (baseAut k K σ) (baseAut_over k K σ)

/-- The Galois-induced base-change map commutes with projection to the source scheme. -/
theorem map_toSource
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    map k K f σ ≫ FieldExtension.toSource k K f =
      FieldExtension.toSource k K f := by
  exact FieldExtension.Equivariance.map_toSource k K f
    (baseAut k K σ) (baseAut_over k K σ)

/-- The Galois-induced base-change map commutes with projection to the extension base. -/
theorem map_toBase
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    map k K f σ ≫ FieldExtension.toBase k K f =
      FieldExtension.toBase k K f ≫ baseAut k K σ := by
  exact FieldExtension.Equivariance.map_toBase k K f
    (baseAut k K σ) (baseAut_over k K σ)

/-- The base-change map attached to the identity Galois automorphism is the identity. -/
theorem map_one
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    map k K f (1 : Gal(K/k)) = 𝟙 _ := by
  have h : baseAut k K (1 : Gal(K/k)) = 𝟙 _ := Spec.map_id _
  simpa only [map, h] using FieldExtension.Equivariance.map_id k K f

/-- Galois multiplication is transported to categorical composition on the pullback. -/
theorem map_mul
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ τ : Gal(K/k)) :
    map k K f (σ * τ) = map k K f σ ≫ map k K f τ := by
  have h : baseAut k K (σ * τ) = baseAut k K σ ≫ baseAut k K τ := by
    dsimp [baseAut]
    rw [← Spec.map_comp]
    congr 1
  simpa only [map, h] using
    (FieldExtension.Equivariance.map_comp k K f
      (baseAut k K σ) (baseAut k K τ)
      (baseAut_over k K σ) (baseAut_over k K τ)).symm

/-- The automorphism of a field-extension base change induced by a Galois element. -/
noncomputable def aut
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    Aut (FieldExtension.baseChange k K f) :=
  { hom := map k K f σ
    inv := map k K f σ.symm
    hom_inv_id := by
      change map k K f σ ≫ map k K f σ⁻¹ = 𝟙 _
      rw [← map_mul, mul_inv_cancel, map_one]
    inv_hom_id := by
      change map k K f σ⁻¹ ≫ map k K f σ = 𝟙 _
      rw [← map_mul, inv_mul_cancel, map_one] }

/-- The hom component of the Galois base-change automorphism is the induced base-change map. -/
theorem aut_hom
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (aut k K f σ).hom = map k K f σ := rfl

/-- The inverse component of the Galois base-change automorphism is induced by `σ.symm`. -/
theorem aut_inv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (aut k K f σ).inv = map k K f σ.symm := rfl

/-- The hom of the Galois base-change automorphism commutes with projection to the source. -/
theorem aut_hom_toSource
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (aut k K f σ).hom ≫ FieldExtension.toSource k K f =
      FieldExtension.toSource k K f := by
  exact map_toSource k K f σ

/-- The hom of the Galois base-change automorphism commutes with projection to the extension base.
-/
theorem aut_hom_toBase
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (aut k K f σ).hom ≫ FieldExtension.toBase k K f =
      FieldExtension.toBase k K f ≫ baseAut k K σ := by
  exact map_toBase k K f σ

/-- The Galois base-change automorphism at one is the identity automorphism. -/
theorem aut_one
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    aut k K f (1 : Gal(K/k)) = 1 := by
  apply Aut.ext
  exact map_one k K f

/-- The Galois base-change automorphisms are anti-multiplicative in `Aut`, whose multiplication
uses reversed categorical composition. -/
theorem aut_mul
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ τ : Gal(K/k)) :
    aut k K f (σ * τ) = aut k K f τ * aut k K f σ := by
  apply Aut.ext
  exact map_mul k K f σ τ

/-- The opposite Galois group acts by a monoid homomorphism on the automorphisms of the
field-extension base change. -/
noncomputable def opAutHom
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    (Gal(K/k))ᵐᵒᵖ →* Aut (FieldExtension.baseChange k K f) where
  toFun σ := aut k K f σ.unop
  map_one' := aut_one k K f
  map_mul' σ τ := aut_mul k K f τ.unop σ.unop

/-- The opposite-Galois automorphism hom evaluates to the automorphism induced by the underlying
Galois element. -/
theorem opAutHom_apply
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : (Gal(K/k))ᵐᵒᵖ) :
    opAutHom k K f σ = aut k K f σ.unop := rfl

end FieldExtension.Galois

end AlgebraicGeometry
