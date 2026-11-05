/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

open scoped TensorProduct

universe u v

namespace MilnorK

/-- The Steinberg generators in the tensor algebra on the additive form of `kˣ`.
Writing the two units as `x` and `y` with `x + y = 1` avoids making a proof-valued
choice of a unit structure on `1 - x`. -/
def steinbergGenerators (k : Type u) [Field k] :
    Set (TensorAlgebra ℤ (Additive kˣ)) :=
  {z | ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
    z = TensorAlgebra.ι ℤ (Additive.ofMul x) *
      TensorAlgebra.ι ℤ (Additive.ofMul y)}

/-- Membership in the set of Steinberg generators is the unit-pair relation `x + y = 1`. -/
theorem mem_steinbergGenerators_iff {k : Type u} [Field k]
    {z : TensorAlgebra ℤ (Additive kˣ)} :
    z ∈ steinbergGenerators k ↔ ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
      z = TensorAlgebra.ι ℤ (Additive.ofMul x) *
        TensorAlgebra.ι ℤ (Additive.ofMul y) := Iff.rfl

/-- The two-sided Steinberg ideal in the tensor algebra on `Additive kˣ`. -/
def steinbergIdeal (k : Type u) [Field k] :
    TwoSidedIdeal (TensorAlgebra ℤ (Additive kˣ)) :=
  TwoSidedIdeal.span (steinbergGenerators k)

/-- Every Steinberg generator belongs to the Steinberg ideal. -/
theorem mem_steinbergIdeal_of_mem_generators {k : Type u} [Field k]
    {z : TensorAlgebra ℤ (Additive kˣ)} (hz : z ∈ steinbergGenerators k) :
    z ∈ steinbergIdeal k := TwoSidedIdeal.subset_span hz

/-- The graded Milnor K-ring of a field, presented as the tensor algebra on `kˣ`
modulo the two-sided Steinberg ideal. -/
abbrev Ring (k : Type u) [Field k] := (steinbergIdeal k).ringCon.Quotient

/-- The canonical quotient map from the tensor algebra to the Milnor K-ring. -/
def quotientMk (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →+* Ring k :=
  (steinbergIdeal k).ringCon.mk'

/-- The canonical map onto the Milnor K-ring is surjective. -/
theorem quotientMk_surjective (k : Type u) [Field k] :
    Function.Surjective (quotientMk k) := (steinbergIdeal k).ringCon.mk'_surjective

/-- A Steinberg generator maps to zero in the Milnor K-ring. -/
theorem quotientMk_steinberg {k : Type u} [Field k]
    (x y : kˣ) (hxy : (x : k) + (y : k) = 1) :
    quotientMk k
      (TensorAlgebra.ι ℤ (Additive.ofMul x) * TensorAlgebra.ι ℤ (Additive.ofMul y)) = 0 := sorry

/-- The degree-`n` part of the Milnor K-ring, as the image of the `n`th tensor power. -/
def degree (n : ℕ) (k : Type u) [Field k] : Submodule ℤ (Ring k) :=
  LinearMap.range ((quotientMk k).toIntAlgHom.toLinearMap.comp
    (TensorPower.toTensorAlgebra :
      (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ)))

/-- The degree-`n` Milnor K-group of `k`. -/
abbrev Group (n : ℕ) (k : Type u) [Field k] := degree n k

/-- The degree submodule is the image of the canonical map from the corresponding tensor power. -/
theorem degree_eq_range (n : ℕ) (k : Type u) [Field k] :
    degree n k = LinearMap.range ((quotientMk k).toIntAlgHom.toLinearMap.comp
      (TensorPower.toTensorAlgebra :
        (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ))) := rfl

/-- A pure tensor maps into the degree-`n` part of the Milnor K-ring. -/
theorem pureSymbol_mem_degree {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) :
    quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))) ∈
      degree n k := by
  refine ⟨PiTensorProduct.tprod ℤ (fun i ↦ Additive.ofMul (x i)), ?_⟩
  change quotientMk k (TensorPower.toTensorAlgebra
    (PiTensorProduct.tprod ℤ (fun i ↦ Additive.ofMul (x i)))) = _
  rw [TensorPower.toTensorAlgebra_tprod]

/-- The pure Milnor symbol associated to an `n`-tuple of units. -/
def symbol {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) : Group n k :=
  ⟨quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))),
    pureSymbol_mem_degree x⟩

/-- The underlying ring element of a pure Milnor symbol is the image of its pure tensor. -/
theorem symbol_coe {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) :
    (symbol x : Ring k) =
      quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))) := rfl

/-- The canonical map from `ℤ` to the degree-zero Milnor K-group. -/
def degreeZeroMap (k : Type u) [Field k] : ℤ →+ Group 0 k where
  toFun n := ⟨quotientMk k (algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ)) n), sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The canonical degree-zero map identifies `ℤ` with `K₀ᴹ(k)`. -/
theorem degreeZeroMap_bijective (k : Type u) [Field k] :
    Function.Bijective (degreeZeroMap k) := sorry

/-- The canonical map from the additive form of `kˣ` to the degree-one Milnor K-group. -/
def degreeOneMap (k : Type u) [Field k] : Additive kˣ →+ Group 1 k where
  toFun x := ⟨quotientMk k (TensorAlgebra.ι ℤ x), sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The canonical degree-one map identifies `Additive kˣ` with `K₁ᴹ(k)`. -/
theorem degreeOneMap_bijective (k : Type u) [Field k] :
    Function.Bijective (degreeOneMap k) := sorry

/-- The degree-two Steinberg relations inside `Additive kˣ ⊗[ℤ] Additive kˣ`. -/
def degreeTwoRelations (k : Type u) [Field k] :
    Submodule ℤ (Additive kˣ ⊗[ℤ] Additive kˣ) :=
  Submodule.span ℤ {z | ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
    z = Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y}

/-- Membership in the degree-two relation submodule is membership in the span of the
Steinberg tensors. -/
theorem mem_degreeTwoRelations_iff {k : Type u} [Field k]
    {z : Additive kˣ ⊗[ℤ] Additive kˣ} :
    z ∈ degreeTwoRelations k ↔ z ∈ Submodule.span ℤ
      {w | ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
        w = Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y} := Iff.rfl

/-- The tensor-product presentation of `K₂ᴹ(k)`. -/
abbrev DegreeTwoPresentation (k : Type u) [Field k] :=
  (Additive kˣ ⊗[ℤ] Additive kˣ) ⧸ degreeTwoRelations k

/-- The bilinear symbol map from the degree-two tensor product into `K₂ᴹ(k)`. -/
def degreeTwoTensorMap (k : Type u) [Field k] :
    (Additive kˣ ⊗[ℤ] Additive kˣ) →ₗ[ℤ] Group 2 k :=
  TensorProduct.lift
    { toFun := fun x ↦
        { toFun := fun y ↦
            ⟨quotientMk k
              (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y), sorry⟩
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }

/-- A pure tensor maps to the product of its two degree-one generators. -/
theorem degreeTwoTensorMap_tmul (k : Type u) [Field k] (x y : kˣ) :
    (degreeTwoTensorMap k
      (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y) : Ring k) =
        quotientMk k
          (TensorAlgebra.ι ℤ (Additive.ofMul x) *
            TensorAlgebra.ι ℤ (Additive.ofMul y)) := sorry

/-- The canonical map from the Steinberg quotient presentation into `K₂ᴹ(k)`. -/
def degreeTwoMap (k : Type u) [Field k] :
    DegreeTwoPresentation k →ₗ[ℤ] Group 2 k :=
  (degreeTwoRelations k).liftQ (degreeTwoTensorMap k) sorry

/-- The Steinberg quotient presentation identifies canonically with `K₂ᴹ(k)`. -/
theorem degreeTwoMap_bijective (k : Type u) [Field k] :
    Function.Bijective (degreeTwoMap k) := sorry

/-- The tensor-power map whose range is the degree-`n` Milnor K-group. -/
def tensorToRing (n : ℕ) (k : Type u) [Field k] :
    (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] Ring k :=
  (quotientMk k).toIntAlgHom.toLinearMap.comp
    (TensorPower.toTensorAlgebra :
      (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ))

/-- The range of `tensorToRing` is the degree-`n` Milnor K-group. -/
theorem tensorToRing_range (n : ℕ) (k : Type u) [Field k] :
    LinearMap.range (tensorToRing n k) = degree n k := rfl

/-- The additive map on units induced by a homomorphism of fields. -/
def unitsHomAdditive {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) :
    Additive kˣ →+ Additive Lˣ where
  toFun x := Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul x))
  map_zero' := sorry
  map_add' := sorry

/-- The tensor-algebra map induced by a homomorphism of fields. -/
def tensorAlgebraMap {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) :
    TensorAlgebra ℤ (Additive kˣ) →ₐ[ℤ] TensorAlgebra ℤ (Additive Lˣ) :=
  TensorAlgebra.lift ℤ <|
    (TensorAlgebra.ι ℤ).comp (unitsHomAdditive f).toIntLinearMap

/-- The induced map of Milnor K-rings along a homomorphism of fields. -/
def mapRing {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) :
    Ring k →+* Ring L :=
  (steinbergIdeal k).ringCon.lift ((quotientMk L).comp (tensorAlgebraMap f).toRingHom) sorry

/-- Applying `mapRing` recovers the image of a tensor-algebra element. -/
theorem mapRing_quotientMk {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L)
    (z : TensorAlgebra ℤ (Additive kˣ)) :
    mapRing f (quotientMk k z) = quotientMk L (tensorAlgebraMap f z) := sorry

/-- The induced map of degree-`n` Milnor K-groups along a homomorphism of fields. -/
def mapGroup {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) (n : ℕ) :
    Group n k →+ Group n L where
  toFun a := ⟨mapRing f a.1, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- A pure symbol is sent to the symbol of the image units. -/
theorem mapGroup_symbol {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L)
    {n : ℕ} (a : Fin n → kˣ) :
    mapGroup f n (symbol a) =
      symbol (fun r ↦ Units.map f.toMonoidHom (a r)) := sorry

/-- Left multiplication by a degree-one generator on the truncation in degrees zero,
one and two. The last component is already taken modulo the Steinberg tensors. -/
noncomputable def degreeShift (k : Type u) [Field k] :
    Additive kˣ →ₗ[ℤ]
      Module.End ℤ (ℤ × Additive kˣ × DegreeTwoPresentation k) where
  toFun x :=
    { toFun := fun p ↦ ((0 : ℤ), p.1 • x, (degreeTwoRelations k).mkQ (x ⊗ₜ[ℤ] p.2.1))
      map_add' := by
        intro p q
        simp [add_smul, TensorProduct.tmul_add]
      map_smul' := by
        intro r p
        simp [smul_smul, TensorProduct.tmul_smul] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro p
    change ((0 : ℤ), p.1 • (x + y), (degreeTwoRelations k).mkQ ((x + y) ⊗ₜ[ℤ] p.2.1)) =
      ((0 : ℤ), p.1 • x, (degreeTwoRelations k).mkQ (x ⊗ₜ[ℤ] p.2.1)) +
      ((0 : ℤ), p.1 • y, (degreeTwoRelations k).mkQ (y ⊗ₜ[ℤ] p.2.1))
    simp [smul_add, TensorProduct.add_tmul]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro p
    change ((0 : ℤ), p.1 • (r • x), (degreeTwoRelations k).mkQ ((r • x) ⊗ₜ[ℤ] p.2.1)) =
      r • ((0 : ℤ), p.1 • x, (degreeTwoRelations k).mkQ (x ⊗ₜ[ℤ] p.2.1))
    simp only [← TensorProduct.smul_tmul', map_smul, Prod.smul_mk, smul_zero]
    rw [smul_comm p.1 r x]

/-- The universal tensor-algebra action on its low-degree Steinberg truncation. -/
noncomputable def tensorLowDegrees (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →ₐ[ℤ]
      Module.End ℤ (ℤ × Additive kˣ × DegreeTwoPresentation k) :=
  TensorAlgebra.lift ℤ (degreeShift k)

/-- A Steinberg tensor has zero class in the degree-two presentation. -/
theorem degreeTwoRelations_mkQ_steinberg (k : Type u) [Field k]
    (x y : kˣ) (hxy : (x : k) + (y : k) = 1) :
    (degreeTwoRelations k).mkQ (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (degreeTwoRelations k)).mpr
  exact Submodule.subset_span ⟨x, y, hxy, rfl⟩

/-- The truncated action kills the entire two-sided Steinberg ideal, so it is
independent of the representative of a Milnor K-class. -/
theorem steinbergIdeal_le_ker_tensorLowDegrees (k : Type u) [Field k] :
    steinbergIdeal k ≤ TwoSidedIdeal.ker (tensorLowDegrees k).toRingHom := by
  apply TwoSidedIdeal.span_le.mpr
  rintro z ⟨x, y, hxy, rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  apply LinearMap.ext
  intro p
  simp [tensorLowDegrees, TensorAlgebra.lift_ι_apply, Module.End.mul_apply,
    degreeShift, TensorProduct.tmul_smul]
  change p.1 • (degreeTwoRelations k).mkQ
    (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y) = 0
  rw [degreeTwoRelations_mkQ_steinberg k x y hxy]
  exact smul_zero p.1

/-- Read the degree-one component by applying the truncated action to the scalar generator. -/
noncomputable def tensorDegreeOne (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →ₗ[ℤ] Additive kˣ where
  toFun z := (tensorLowDegrees k z (1, 0, 0)).2.1
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- Read the degree-two component, already modulo Steinberg relations. -/
noncomputable def tensorDegreeTwo (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →ₗ[ℤ] DegreeTwoPresentation k where
  toFun z := (tensorLowDegrees k z (1, 0, 0)).2.2
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- Quadratic Steinberg relations do not change the first tensor component. -/
theorem tensorDegreeOne_respects_steinberg (k : Type u) [Field k] :
    (steinbergIdeal k).ringCon.toAddCon ≤
      AddCon.ker (tensorDegreeOne k).toAddMonoidHom := by
  intro a b hab
  have h := (TwoSidedIdeal.ringCon_le_iff.mp
    (steinbergIdeal_le_ker_tensorLowDegrees k)) hab
  exact congrArg (fun f : Module.End ℤ (ℤ × Additive kˣ × DegreeTwoPresentation k) ↦
    (f (1, 0, 0)).2.1) h

/-- The second component of the Steinberg ideal lies in the degree-two relation submodule. -/
theorem tensorDegreeTwo_respects_steinberg (k : Type u) [Field k] :
    (steinbergIdeal k).ringCon.toAddCon ≤
      AddCon.ker (tensorDegreeTwo k).toAddMonoidHom := by
  intro a b hab
  have h := (TwoSidedIdeal.ringCon_le_iff.mp
    (steinbergIdeal_le_ker_tensorLowDegrees k)) hab
  exact congrArg (fun f : Module.End ℤ (ℤ × Additive kˣ × DegreeTwoPresentation k) ↦
    (f (1, 0, 0)).2.2) h

/-- The first tensor component descends along the additive quotient of the Milnor ring. -/
noncomputable def degreeOneProjection (k : Type u) [Field k] : Group 1 k →+ Additive kˣ :=
  ((steinbergIdeal k).ringCon.toAddCon.lift
    (tensorDegreeOne k).toAddMonoidHom (tensorDegreeOne_respects_steinberg k)).comp
      (degree 1 k).subtype.toAddMonoidHom

/-- The second tensor component descends to the Steinberg tensor presentation. -/
noncomputable def degreeTwoProjection (k : Type u) [Field k] :
    Group 2 k →+ DegreeTwoPresentation k :=
  ((steinbergIdeal k).ringCon.toAddCon.lift
    (tensorDegreeTwo k).toAddMonoidHom (tensorDegreeTwo_respects_steinberg k)).comp
      (degree 2 k).subtype.toAddMonoidHom

/-- The first component recovers a degree-one generator. -/
theorem degreeOneProjection_degreeOneMap (k : Type u) [Field k] (x : Additive kˣ) :
    degreeOneProjection k (degreeOneMap k x) = x := by
  change (tensorLowDegrees k (TensorAlgebra.ι ℤ x) (1, 0, 0)).2.1 = x
  simp [tensorLowDegrees, TensorAlgebra.lift_ι_apply, degreeShift]

/-- Every degree-one class is represented by its first tensor component. -/
theorem degreeOneMap_degreeOneProjection (k : Type u) [Field k] (x : Group 1 k) :
    degreeOneMap k (degreeOneProjection k x) = x := by
  obtain ⟨y, rfl⟩ := (degreeOneMap_bijective k).surjective x
  rw [degreeOneProjection_degreeOneMap]

/-- The second component recovers the degree-two tensor presentation. -/
theorem degreeTwoProjection_degreeTwoMap (k : Type u) [Field k]
    (x : DegreeTwoPresentation k) :
    degreeTwoProjection k (degreeTwoMap k x) = x := by
  refine Submodule.Quotient.induction_on (degreeTwoRelations k) x ?_
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro a b
    change tensorDegreeTwo k
      (TensorAlgebra.ι ℤ a * TensorAlgebra.ι ℤ b) =
        (degreeTwoRelations k).mkQ (a ⊗ₜ[ℤ] b)
    simp [tensorDegreeTwo, tensorLowDegrees, TensorAlgebra.lift_ι_apply,
      Module.End.mul_apply, degreeShift]
  · intro a b ha hb
    simpa only [Submodule.Quotient.mk_add, map_add, ha, hb]

/-- Every degree-two class is represented by its second tensor component. -/
theorem degreeTwoMap_degreeTwoProjection (k : Type u) [Field k] (x : Group 2 k) :
    degreeTwoMap k (degreeTwoProjection k x) = x := by
  obtain ⟨y, rfl⟩ := (degreeTwoMap_bijective k).surjective x
  rw [degreeTwoProjection_degreeTwoMap]

/-- The canonical identification of `Additive kˣ` with `K₁ᴹ(k)`. -/
noncomputable def degreeOneEquiv (k : Type u) [Field k] :
    Additive kˣ ≃+ Group 1 k where
  toFun := degreeOneMap k
  invFun := degreeOneProjection k
  left_inv := degreeOneProjection_degreeOneMap k
  right_inv := degreeOneMap_degreeOneProjection k
  map_add' := (degreeOneMap k).map_add

/-- The canonical identification of the Steinberg presentation with `K₂ᴹ(k)`. -/
noncomputable def degreeTwoEquiv (k : Type u) [Field k] :
    DegreeTwoPresentation k ≃+ Group 2 k where
  toFun := degreeTwoMap k
  invFun := degreeTwoProjection k
  left_inv := degreeTwoProjection_degreeTwoMap k
  right_inv := degreeTwoMap_degreeTwoProjection k
  map_add' := (degreeTwoMap k).map_add

end MilnorK
