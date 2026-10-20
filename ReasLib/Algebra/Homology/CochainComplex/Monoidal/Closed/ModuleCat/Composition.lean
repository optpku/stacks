/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Source

/-!
# Coordinates of composition on module-valued Hom complexes

The complex map `InternalHom.Module.comp` is the canonical owner.  This leaf exposes its
homogeneous coordinates without unfolding the closed-monoidal construction.  A raw coordinate
composes two selected homogeneous maps; the full component additionally transports the target to
the chosen total degree.

@stack 0A8I
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex

namespace CategoryTheory.CochainComplex.InternalHom.Module.Composition

variable {R : Type u} [CommRing R]

/-- The raw `(t, r, p)` coordinate of composition of module-valued Hom complexes. -/
@[stacks 0A8I "homogeneous coordinate of Hom-complex composition"]
noncomputable def coordinate
    (K L M : CochainComplex (ModuleCat R) ℤ) (t r p : ℤ) :
    (moduleComplex R L M).X t ⊗ (moduleComplex R K L).X r ⟶
      (ihom (K.X p)).obj (M.X ((p + r) + t)) :=
  (proj R L M t (p + r) ⊗ₘ proj R K L r p) ≫
    MonoidalClosed.Source.comp (K.X p) (L.X (p + r)) (M.X ((p + r) + t))

/-- The full `(t, r, p)` component restricts composition to a tensor summand and then projects
the target Hom complex at source degree `p`. -/
@[stacks 0A8I "component of Hom-complex composition"]
noncomputable def component
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) :
    (moduleComplex R L M).X t ⊗ (moduleComplex R K L).X r ⟶
      degreeFamily R K M n p :=
  HomologicalComplex.ιTensorObj
      (moduleComplex R L M) (moduleComplex R K L) t r n h ≫
    (InternalHom.Module.comp K L M).f n ≫ proj R K M n p

/-- Total-degree bookkeeping identifies the raw composite target with the target of the full
component. -/
theorem targetIndex {t r n p : ℤ} (h : t + r = n) :
    (p + r) + t = p + n := sorry

/-- The full component is the raw coordinate followed by target-degree transport. -/
theorem component_factor
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) :
    component K L M t r n p h =
      coordinate K L M t r p ≫
        (ihom (K.X p)).map (eqToHom (congrArg M.X (targetIndex h))) := sorry

/-- Restricting composition to a tensor summand and a target projection gives its full
component. -/
@[simp]
theorem ι_comp_f_proj
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj
          (moduleComplex R L M) (moduleComplex R K L) t r n h ≫
        (InternalHom.Module.comp K L M).f n ≫ proj R K M n p =
      component K L M t r n p h := sorry

/-- On a pure tensor, a raw coordinate is ordinary composition of the two selected homogeneous
maps. -/
@[simp]
theorem coordinate_tmul_apply
    (K L M : CochainComplex (ModuleCat R) ℤ) (t r p : ℤ)
    (g : (moduleComplex R L M).X t) (f : (moduleComplex R K L).X r)
    (k : K.X p) :
    ModuleCat.Hom.hom
        ((coordinate K L M t r p).hom (TensorProduct.tmul R g f)) k =
      ModuleCat.Hom.hom ((proj R L M t (p + r)).hom g)
        (ModuleCat.Hom.hom ((proj R K L r p).hom f) k) := sorry

/-- On a pure tensor, the full component is homogeneous composition followed by total-degree
transport. -/
@[stacks 0A8I "pure-tensor formula for Hom-complex composition"]
theorem component_tmul_apply
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n)
    (g : (moduleComplex R L M).X t) (f : (moduleComplex R K L).X r)
    (k : K.X p) :
    ModuleCat.Hom.hom
        ((component K L M t r n p h).hom (TensorProduct.tmul R g f)) k =
      ModuleCat.Hom.hom (eqToHom (congrArg M.X (targetIndex h)))
        (ModuleCat.Hom.hom ((proj R L M t (p + r)).hom g)
          (ModuleCat.Hom.hom ((proj R K L r p).hom f) k)) := sorry

end CategoryTheory.CochainComplex.InternalHom.Module.Composition
