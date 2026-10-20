/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Regular

/-!
# The divided-differential model of the Berthelot-Ogus eta operator

For a `ℤ`-indexed cochain complex on which multiplication by `f` is injective, this file models
the Berthelot-Ogus eta operator in coordinates.  Its degree-`i` term is

`{x : K.X i | K.d i (i + 1) x ∈ f • K.X (i + 1)}`,

and its differential sends `x` to the unique `y` such that `f • y = d x`.  This model is
independent of `i`, so it represents negative degrees faithfully and never replaces an integer
exponent by `Int.toNat`.
@stack 0F7P
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- The integer-cochain specialization of shape-independent termwise scalar regularity. -/
@[stacks 0F7P "termwise regular integer-indexed eta complexes"]
abbrev IsTermwiseTorsionFree (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) : Prop :=
  K.IsTermwiseSMulRegular f

/-- Termwise `f`-torsion-freeness is exactly degreewise `f`-regularity. -/
theorem isTermwiseTorsionFree_iff (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsTermwiseTorsionFree f K ↔ ∀ i : ℤ, IsSMulRegular (K.X i) f := sorry

/-- The canonical category of integer-indexed complexes on which multiplication by `f` is
degreewise injective. -/
@[stacks 0F7P "regular domain of the integer-indexed eta functor"]
abbrev Domain (f : A) :=
  HomologicalComplex.RegularDomain (c := ComplexShape.up ℤ) f

/-- The degree-`i` term in divided-differential coordinates: the elements whose differential is
divisible by `f`. -/
@[stacks 0F7P "divided-differential eta term"]
def term (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    Submodule A (K.X i) :=
  (LinearMap.range (LinearMap.lsmul A (K.X (i + 1)) f)).comap (K.d i (i + 1)).hom

/-- The ambient differential of an eta term lies in the range of multiplication by `f`. -/
theorem d_mem_range (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (x : term f K i) :
    K.d i (i + 1) x ∈ LinearMap.range (LinearMap.lsmul A (K.X (i + 1)) f) := sorry

/-- The differential of `K`, with codomain restricted to the range of multiplication by `f`. -/
def dToRange (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    term f K i →ₗ[A] LinearMap.range (LinearMap.lsmul A (K.X (i + 1)) f) :=
  ((K.d i (i + 1)).hom.comp (term f K i).subtype).codRestrict _ (d_mem_range f K i)

/-- Division of the differential by `f`.  The inverse is taken only on the range of scalar
multiplication, where termwise torsion-freeness makes it canonical. -/
noncomputable def divideLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f) : term f K i →ₗ[A] K.X (i + 1) :=
  (LinearEquiv.ofInjective (LinearMap.lsmul A (K.X (i + 1)) f) hnext).symm.toLinearMap.comp
    (dToRange f K i)

/-- Division by `f` is characterized by multiplying the result back by `f`. -/
theorem divide_spec (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f) (x : term f K i) :
    f • divideLinear f K i hnext x = K.d i (i + 1) x := sorry

/-- The divided differential is the unique solution of `f • y = d x`. -/
theorem divide_unique (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f) (x : term f K i) (y : K.X (i + 1))
    (hy : f • y = K.d i (i + 1) x) : y = divideLinear f K i hnext x := sorry

/-- Dividing the differential of an eta term by `f` produces an eta term in the next degree. -/
theorem divide_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f)
    (hnext₂ : IsSMulRegular (K.X ((i + 1) + 1)) f) (x : term f K i) :
    divideLinear f K i hnext x ∈ term f K (i + 1) := sorry

/-- The differential on the divided-differential eta complex. -/
def dLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f)
    (hnext₂ : IsSMulRegular (K.X ((i + 1) + 1)) f) :
    term f K i →ₗ[A] term f K (i + 1) :=
  (divideLinear f K i hnext).codRestrict _ (divide_mem f K i hnext hnext₂)

/-- Two successive divided differentials compose to zero. -/
theorem d_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f)
    (hnext₂ : IsSMulRegular (K.X ((i + 1) + 1)) f)
    (hnext₃ : IsSMulRegular (K.X (((i + 1) + 1) + 1)) f) :
    ModuleCat.ofHom (dLinear f K i hnext hnext₂) ≫
      ModuleCat.ofHom (dLinear f K (i + 1) hnext₂ hnext₃) = 0 := sorry

/-- The `ℤ`-indexed Berthelot-Ogus eta complex in divided-differential coordinates. -/
@[stacks 0F7P "Berthelot-Ogus eta complex in divided-differential coordinates"]
def eta (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) : CochainComplex (ModuleCat.{v} A) ℤ :=
  CochainComplex.of
    (fun i ↦ ModuleCat.of A (term f K i))
    (fun i ↦ ModuleCat.ofHom (dLinear f K i (hK.degree (i + 1))
      (hK.degree ((i + 1) + 1))))
    (fun i ↦ d_comp_d f K i (hK.degree (i + 1)) (hK.degree ((i + 1) + 1))
      (hK.degree (((i + 1) + 1) + 1)))

/-- The terms of the divided-differential eta complex are the divisibility submodules. -/
@[simp]
theorem eta_X (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) (i : ℤ) :
    (eta f K hK).X i = ModuleCat.of A (term f K i) := sorry

/-- The differential of the divided-differential eta complex is division by `f`. -/
@[simp]
theorem eta_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) (i : ℤ) :
    (eta f K hK).d i (i + 1) = ModuleCat.ofHom
      (dLinear f K i (hK.degree (i + 1)) (hK.degree ((i + 1) + 1))) := sorry

/-- A cochain map preserves the divided-differential eta terms. -/
theorem map_mem (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (i : ℤ) (x : term f K i) : φ.f i x ∈ term f L i := sorry

/-- The degree-`i` map on divided-differential eta terms induced by a cochain map. -/
def mapLinear (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (i : ℤ) : term f K i →ₗ[A] term f L i :=
  ((φ.f i).hom.comp (term f K i).subtype).codRestrict _ (map_mem f φ i)

/-- The induced term maps commute with the divided differentials. -/
theorem map_comm (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (hK : K.IsTermwiseSMulRegular f) (hL : L.IsTermwiseSMulRegular f)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    ModuleCat.ofHom (mapLinear f φ i) ≫ (eta f L hL).d i j =
      (eta f K hK).d i j ≫ ModuleCat.ofHom (mapLinear f φ j) := sorry

/-- The map on divided-differential eta complexes induced by a cochain map. -/
def map (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (hK : K.IsTermwiseSMulRegular f) (hL : L.IsTermwiseSMulRegular f) :
    eta f K hK ⟶ eta f L hL where
  f i := ModuleCat.ofHom (mapLinear f φ i)
  comm' i j hij := map_comm f φ hK hL i j hij

/-- The divided-differential eta construction sends identity maps to identity maps. -/
@[simp]
theorem map_id (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : K.IsTermwiseSMulRegular f) : map f (𝟙 K) hK hK = 𝟙 (eta f K hK) := sorry

/-- The divided-differential eta construction preserves composition. -/
@[simp]
theorem map_comp (f : A) {K L M : CochainComplex (ModuleCat.{v} A) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (hK : K.IsTermwiseSMulRegular f)
    (hL : L.IsTermwiseSMulRegular f) (hM : M.IsTermwiseSMulRegular f) :
    map f (φ ≫ ψ) hK hM = map f φ hK hL ≫ map f ψ hL hM := sorry

/-- The divided-differential eta construction preserves addition of cochain maps. -/
theorem map_add (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (φ ψ : K ⟶ L) (hK : K.IsTermwiseSMulRegular f)
    (hL : L.IsTermwiseSMulRegular f) :
    map f (φ + ψ) hK hL = map f φ hK hL + map f ψ hK hL := sorry

/-- The divided differential is natural for cochain maps, under only the degree-local regularity
needed to divide in the source and target. -/
theorem divideLinear_naturality (f : A)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L) (i : ℤ)
    (hK : IsSMulRegular (K.X (i + 1)) f)
    (hL : IsSMulRegular (L.X (i + 1)) f) :
    ModuleCat.ofHom (mapLinear f φ i) ≫ ModuleCat.ofHom (divideLinear f L i hL) =
      ModuleCat.ofHom (divideLinear f K i hK) ≫ φ.f (i + 1) := sorry

/-- The degree components of the induced eta map are the restricted ambient maps. -/
@[simp]
theorem map_f (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (hK : K.IsTermwiseSMulRegular f) (hL : L.IsTermwiseSMulRegular f) (i : ℤ) :
    (map f φ hK hL).f i = ModuleCat.ofHom (mapLinear f φ i) := sorry

/-- The divided-differential eta construction as a functor on its canonical regular domain. -/
@[stacks 0F7P "functorial divided-differential eta construction"]
def functor (f : A) :
    Domain f ⥤ CochainComplex (ModuleCat.{v} A) ℤ where
  obj K := eta f K.obj K.property
  map {K L} φ := map f φ.hom K.property L.property
  map_id K := map_id f K.obj K.property
  map_comp {K L M} φ ψ := map_comp f φ.hom ψ.hom K.property L.property M.property

/-- The object part of the divided-differential eta functor is the eta complex of the underlying
complex. -/
@[simp]
theorem functor_obj (f : A) (K : Domain f) :
    (functor f).obj K = eta f K.obj K.property := sorry

/-- The morphism part of the divided-differential eta functor is the canonical eta map. -/
@[simp]
theorem functor_map (f : A) {K L : Domain f} (φ : K ⟶ L) :
    (functor f).map φ = map f φ.hom K.property L.property := sorry

/-- The eta complex of a termwise `f`-torsion-free complex is again termwise
`f`-torsion-free. -/
theorem eta_isTermwiseTorsionFree (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) : IsTermwiseTorsionFree f (eta f K hK) := sorry

/-- The divided-differential eta construction as an endofunctor of its canonical regular
domain. -/
def domainFunctor (f : A) : Domain f ⥤ Domain f :=
  ObjectProperty.lift _ (functor f)
    (fun K ↦ eta_isTermwiseTorsionFree f K.obj K.property)

/-- The divided-differential eta functor is additive. -/
instance functor_additive (f : A) : (functor f).Additive := sorry

/-- The eta endofunctor of the regular domain is additive. -/
instance domainFunctor_additive (f : A) : (domainFunctor f).Additive := sorry

end CochainComplex.BerthelotOgus.Int
