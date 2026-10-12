/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Source
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Coordinates of the iterated Hom-complex comparison

The canonical map
`Hom^•(L, M) ⊗ K ⟶ Hom^•(Hom^•(K, L), M)` is owned by
`CategoryTheory.CochainComplex.InternalHom.Module.iterated`.  This leaf records the reusable
coordinate API needed for degreewise calculations.  It distinguishes the raw coordinate, whose
inner source is one homogeneous map module, from the full component obtained by precomposing with
the projection out of `Hom^•(K, L)`.

@stack 0A60
@stack 0A61
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex

namespace CategoryTheory.CochainComplex.InternalHom.Module.Iterated

variable {R : Type u} [CommRing R]

/-- The raw `(t, r, p)` coordinate of the tensor-to-iterated-Hom comparison.  Its target retains
the computed degree `(r + p) + t`; total-degree reindexing belongs to the full component API. -/
@[stacks 0A60 "raw coordinate of the tensor-to-iterated Hom comparison"]
noncomputable def coordinate (K L M : CochainComplex (ModuleCat R) ℤ) (t r p : ℤ) :
    (moduleComplex R L M).X t ⊗ K.X r ⟶
      (ihom (degreeFamily R K L p r)).obj (M.X ((r + p) + t)) :=
  (r * p).negOnePow •
    ((proj R L M t (r + p) ⊗ₘ 𝟙 (K.X r)) ≫
      MonoidalClosed.Source.Iterated.map
        (K.X r) (L.X (r + p)) (M.X ((r + p) + t)))

/-- The full `(t, r, p)` component is the canonical complex map restricted to the `(t, r)` tensor
summand and then projected to outer Hom-complex coordinate `p`. -/
@[stacks 0A60 "component of the iterated Hom comparison"]
noncomputable def component (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) :
    (moduleComplex R L M).X t ⊗ K.X r ⟶
      degreeFamily R (moduleComplex R K L) M n p :=
  HomologicalComplex.ιTensorObj (moduleComplex R L M) K t r n h ≫
    (InternalHom.Module.iterated K L M).f n ≫
      proj R (moduleComplex R K L) M n p

/-- Total-degree bookkeeping identifies the computed target of a raw coordinate with the target of
the corresponding full component. -/
theorem targetIndex {t r n p : ℤ} (h : t + r = n) :
    (r + p) + t = p + n := sorry

/-- The full component is the raw coordinate followed by target-degree transport and
precomposition with the inner Hom-complex projection. -/
theorem component_factor (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) :
    component K L M t r n p h =
      coordinate K L M t r p ≫
        (ihom (degreeFamily R K L p r)).map
          (eqToHom (congrArg M.X (targetIndex h))) ≫
        (MonoidalClosed.pre (proj R K L p r)).app (M.X (p + n)) := sorry

/-- Restricting the canonical iterated comparison to a tensor summand and an outer projection is
the corresponding full component. -/
@[simp]
theorem ι_iterated_f_proj (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj (moduleComplex R L M) K t r n h ≫
        (InternalHom.Module.iterated K L M).f n ≫
        proj R (moduleComplex R K L) M n p =
      component K L M t r n p h := sorry

/-- On a pure tensor, a raw coordinate is signed nested evaluation at one homogeneous map. -/
@[simp]
theorem coordinate_tmul_apply (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r p : ℤ) (g : (moduleComplex R L M).X t) (k : K.X r)
    (φ : degreeFamily R K L p r) :
    ModuleCat.Hom.hom
        ((coordinate K L M t r p).hom (TensorProduct.tmul R g k)) φ =
      (r * p).negOnePow •
        ModuleCat.Hom.hom ((proj R L M t (r + p)).hom g)
          (ModuleCat.Hom.hom φ k) := sorry

/-- On a pure tensor and a full inner cochain, a component evaluates through the selected inner
and outer homogeneous projections. -/
@[stacks 0A60 "pure-tensor formula for the iterated Hom comparison"]
theorem component_tmul_apply (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n)
    (g : (moduleComplex R L M).X t) (k : K.X r)
    (φ : (moduleComplex R K L).X p) :
    ModuleCat.Hom.hom
        ((component K L M t r n p h).hom (TensorProduct.tmul R g k)) φ =
      (r * p).negOnePow •
        ModuleCat.Hom.hom (eqToHom (congrArg M.X (targetIndex h)))
          (ModuleCat.Hom.hom ((proj R L M t (r + p)).hom g)
            (ModuleCat.Hom.hom ((proj R K L p r).hom φ) k)) := sorry

/-- On a single inner coordinate at the tensor degree, the abstract iterated-Hom comparison is
the signed nested evaluation used in the direct construction. -/
@[stacks 0A61 "diagonal coordinate of the abstract iterated Hom comparison"]
theorem component_tmul_single_apply
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n)
    (g : (moduleComplex R L M).X t) (k : K.X r)
    (φ : K.X r ⟶ L.X (r + p)) :
    ModuleCat.Hom.hom
        ((component K L M t r n p h).hom (TensorProduct.tmul R g k))
        (Cochain.single φ p) =
      (r * p).negOnePow •
        ModuleCat.Hom.hom (eqToHom (congrArg M.X (targetIndex h)))
          (ModuleCat.Hom.hom ((proj R L M t (r + p)).hom g)
            (ModuleCat.Hom.hom φ k)) := sorry

/-- A single inner coordinate whose source degree differs from the tensor degree contributes
nothing to the abstract iterated-Hom comparison. -/
theorem component_tmul_single_apply_of_ne
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r r' n p : ℤ) (h : t + r = n) (hrr' : r ≠ r')
    (g : (moduleComplex R L M).X t) (k : K.X r)
    (φ : K.X r' ⟶ L.X (r' + p)) :
    ModuleCat.Hom.hom
        ((component K L M t r n p h).hom (TensorProduct.tmul R g k))
        (Cochain.single φ p) = 0 := sorry

/-- A tensor summand with zero right-hand term contributes no component to the iterated-Hom
comparison. -/
theorem component_eq_zero_of_right_isZero
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) (hr : IsZero (K.X r)) :
    component K L M t r n p h = 0 := sorry

/-- A component vanishes when its selected term of the middle complex is zero. -/
theorem component_eq_zero_of_middle_isZero
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) (hp : IsZero (L.X (r + p))) :
    component K L M t r n p h = 0 := sorry

/-- A component vanishes when its selected term of the target complex is zero. -/
theorem component_eq_zero_of_target_isZero
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (t r n p : ℤ) (h : t + r = n) (hp : IsZero (M.X (p + n))) :
    component K L M t r n p h = 0 := sorry

/-- On the diagonal `q + r = p`, the braiding sign in the iterated-Hom coordinate is the sign in
the direct three-index formula. -/
@[stacks 0A61 "diagonal sign in the iterated Hom comparison"]
theorem coordinate_sign {q r p : ℤ} (h : q + r = p) :
    (r * p).negOnePow = (r + q * r).negOnePow := sorry

/-- The fixed-`r` component block packages every outer Hom-complex projection of the degree-`n`
comparison map. -/
@[stacks 0A60 "fixed-degree component block of the iterated Hom comparison"]
noncomputable def componentBlock
    (K L M : CochainComplex (ModuleCat R) ℤ) (n r : ℤ) :
    (moduleComplex R L M).X (n - r) ⊗ K.X r ⟶
      ∏ᶜ (degreeFamily R (moduleComplex R K L) M n) :=
  HomologicalComplex.ιTensorObj (moduleComplex R L M) K
        (n - r) r n (sub_add_cancel n r) ≫
    (InternalHom.Module.iterated K L M).f n ≫
      (degreeIso R (moduleComplex R K L) M n).inv

/-- Projection from a fixed-`r` component block recovers the corresponding full component. -/
@[reassoc (attr := simp)]
theorem componentBlock_π
    (K L M : CochainComplex (ModuleCat R) ℤ) (n r p : ℤ) :
    componentBlock K L M n r ≫
        Pi.π (degreeFamily R (moduleComplex R K L) M n) p =
      component K L M (n - r) r n p (sub_add_cancel n r) := sorry

/-- Reassembling a component block through the Hom-complex degree decomposition is the restriction
of the iterated comparison to the corresponding tensor summand. -/
theorem componentBlock_degreeIso_hom
    (K L M : CochainComplex (ModuleCat R) ℤ) (n r : ℤ) :
    componentBlock K L M n r ≫
        (degreeIso R (moduleComplex R K L) M n).hom =
      HomologicalComplex.ιTensorObj (moduleComplex R L M) K
          (n - r) r n (sub_add_cancel n r) ≫
        (InternalHom.Module.iterated K L M).f n := sorry

/-- The target family of the fixed-`r` raw coordinate block in total degree `n`. -/
@[stacks 0A60 "target family of an iterated Hom coordinate block"]
abbrev blockFamily (K L M : CochainComplex (ModuleCat R) ℤ) (n r p : ℤ) :
    ModuleCat R :=
  (ihom (degreeFamily R K L p r)).obj (M.X ((r + p) + (n - r)))

/-- The fixed-`r` block packages all raw `p`-coordinates before precomposition with the inner
Hom-complex projections. -/
@[stacks 0A60 "raw coordinate block of the iterated Hom comparison"]
noncomputable def block (K L M : CochainComplex (ModuleCat R) ℤ) (n r : ℤ) :
    (moduleComplex R L M).X (n - r) ⊗ K.X r ⟶
      ∏ᶜ (blockFamily K L M n r) :=
  Pi.lift fun p ↦ coordinate K L M (n - r) r p

/-- Projection from a fixed-`r` block recovers its raw `p`-coordinate. -/
@[reassoc (attr := simp)]
theorem block_π (K L M : CochainComplex (ModuleCat R) ℤ) (n r p : ℤ) :
    block K L M n r ≫ Pi.π (blockFamily K L M n r) p =
      coordinate K L M (n - r) r p := sorry

/-- A finite projective tensor term makes its fixed-degree coordinate block an isomorphism. -/
@[stacks 0A60 "finite-projective block of the iterated Hom comparison"]
instance block_isIso (K L M : CochainComplex (ModuleCat R) ℤ) (n r : ℤ)
    [Module.Finite R (K.X r)] [Module.Projective R (K.X r)] :
    IsIso (block K L M n r) := sorry

end CategoryTheory.CochainComplex.InternalHom.Module.Iterated
