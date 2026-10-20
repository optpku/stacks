/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic

/-!
# Relative field spectra and Galois actions

Field extensions induce canonical morphisms of spectra over a base scheme.
Inverting Galois automorphisms gives a left action on the extension spectrum.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension

/-- The spectrum of a field over a scheme via the given structure morphism. -/
abbrev specOver {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) : Over S :=
  Over.mk σ

/-- The relative field spectrum is the slice object of its structure morphism. -/
theorem specOver_eq {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) :
    specOver σ = Over.mk σ := rfl

/-- The extension field spectrum over the base via the canonical spectrum projection. -/
def specExtend {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    Over S :=
  Over.mk (specMap k k' ≫ σ)

/-- The structure map of the extension spectrum factors through the original field spectrum. -/
theorem specExtend_hom {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    (specExtend σ k').hom = specMap k k' ≫ σ := rfl

/-- The canonical projection of field spectra as a morphism over the base scheme. -/
def specExtendToOver {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    specExtend σ k' ⟶ specOver σ :=
  Over.homMk (specMap k k')

/-- The underlying map of the relative projection is the canonical field spectrum map. -/
theorem specExtendToOver_left {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    (specExtendToOver σ k').left = specMap k k' := rfl

namespace Galois

/-- The left Galois action on the extension spectrum uses the inverse field automorphism. -/
def specAut {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    Gal(k'/k) →* Aut (Spec (CommRingCat.of k')) where
  toFun g :=
    { hom := baseAut k k' (g⁻¹)
      inv := baseAut k k' g
      hom_inv_id := by
        dsimp [baseAut]
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext x
        exact g.symm_apply_apply x
      inv_hom_id := by
        dsimp [baseAut]
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext x
        exact g.apply_symm_apply x }
  map_one' := by
    apply Aut.ext
    change baseAut k k' ((1 : Gal(k'/k))⁻¹) = 𝟙 _
    simp only [inv_one]
    exact Spec.map_id _
  map_mul' g h := by
    apply Aut.ext
    change baseAut k k' ((g * h)⁻¹) = baseAut k k' (h⁻¹) ≫ baseAut k k' (g⁻¹)
    dsimp [baseAut]
    rw [← Spec.map_comp]
    congr 1

/-- The spectrum action of a Galois element is induced by its inverse field automorphism. -/
theorem specAut_hom {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (g : Gal(k'/k)) :
    (specAut g).hom = baseAut k k' (g⁻¹) := rfl

end Galois

end AlgebraicGeometry.FieldExtension
