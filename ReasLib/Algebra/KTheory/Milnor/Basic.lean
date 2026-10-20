module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
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
        TensorAlgebra.ι ℤ (Additive.ofMul y) := sorry

/-- The two-sided Steinberg ideal in the tensor algebra on `Additive kˣ`. -/
def steinbergIdeal (k : Type u) [Field k] :
    TwoSidedIdeal (TensorAlgebra ℤ (Additive kˣ)) :=
  TwoSidedIdeal.span (steinbergGenerators k)

/-- Every Steinberg generator belongs to the Steinberg ideal. -/
theorem mem_steinbergIdeal_of_mem_generators {k : Type u} [Field k]
    {z : TensorAlgebra ℤ (Additive kˣ)} (hz : z ∈ steinbergGenerators k) :
    z ∈ steinbergIdeal k := sorry

/-- The graded Milnor K-ring of a field, presented as the tensor algebra on `kˣ`
modulo the two-sided Steinberg ideal. -/
abbrev Ring (k : Type u) [Field k] := (steinbergIdeal k).ringCon.Quotient

/-- The canonical quotient map from the tensor algebra to the Milnor K-ring. -/
def quotientMk (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →+* Ring k :=
  (steinbergIdeal k).ringCon.mk'

/-- The canonical map onto the Milnor K-ring is surjective. -/
theorem quotientMk_surjective (k : Type u) [Field k] :
    Function.Surjective (quotientMk k) := sorry

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
        (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ))) := sorry

/-- A pure tensor maps into the degree-`n` part of the Milnor K-ring. -/
theorem pureSymbol_mem_degree {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) :
    quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))) ∈
      degree n k := sorry

/-- The pure Milnor symbol associated to an `n`-tuple of units. -/
def symbol {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) : Group n k :=
  ⟨quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))),
    pureSymbol_mem_degree x⟩

/-- The underlying ring element of a pure Milnor symbol is the image of its pure tensor. -/
theorem symbol_coe {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) :
    (symbol x : Ring k) =
      quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))) := sorry

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
        w = Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y} := sorry

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
    LinearMap.range (tensorToRing n k) = degree n k := sorry

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

/-- The canonical identification of `Additive kˣ` with `K₁ᴹ(k)`. -/
noncomputable def degreeOneEquiv (k : Type u) [Field k] :
    Additive kˣ ≃+ Group 1 k :=
  AddEquiv.ofBijective (degreeOneMap k) (degreeOneMap_bijective k)

/-- The canonical identification of the Steinberg presentation with `K₂ᴹ(k)`. -/
noncomputable def degreeTwoEquiv (k : Type u) [Field k] :
    DegreeTwoPresentation k ≃+ Group 2 k :=
  AddEquiv.ofBijective (degreeTwoMap k).toAddMonoidHom (degreeTwoMap_bijective k)

end MilnorK
