module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Galois automorphisms of field-extension base changes of algebraic spaces

The fibre product `Spec K ×_{Spec k} X` of an algebraic space `X` over a field `k`
carries a canonical action of `Gal(K/k)ᵐᵒᵖ` by automorphisms over `Spec k`, induced
by `Spec(σ) × id`. The construction applies to arbitrary field extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

/-- The algebraic space `Spec K` over `Spec k` associated to a field extension `K/k`. -/
abbrev specOver (k K : Type u) [Field k] [Field K] [Algebra k K] :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  ofOver (Over.mk (AlgebraicGeometry.FieldExtension.specMap k K))

/-- The base change of an algebraic space `X` over `Spec k` along `Spec K ⟶ Spec k`,
as the fibre product `Spec K ×_{Spec k} X` in algebraic spaces over `Spec k`. -/
abbrev baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  product (specOver k K) X

/-- The projection of the field-extension base change onto `Spec K` over `Spec k`. -/
abbrev baseChangeFst (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    baseChange k K X ⟶ specOver k K :=
  productFst (specOver k K) X

/-- The projection of the field-extension base change onto `X`. -/
abbrev baseChangeSnd (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    baseChange k K X ⟶ X :=
  productSnd (specOver k K) X

namespace Galois

/-- The endomorphism of `Spec K` over `Spec k` induced by a `k`-automorphism of `K`. -/
def specAut (k K : Type u) [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) :
    specOver k K ⟶ specOver k K :=
  ofOverHomMk (AlgebraicGeometry.FieldExtension.Galois.baseAut k K σ)
    (AlgebraicGeometry.FieldExtension.Galois.baseAut_over k K σ)

/-- `specAut σ` is the algebraic-space morphism over `Spec k` induced by `Spec(σ)`. -/
theorem specAut_eq (k K : Type u) [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) :
    specAut k K σ =
      ofOverHomMk (AlgebraicGeometry.FieldExtension.Galois.baseAut k K σ)
        (AlgebraicGeometry.FieldExtension.Galois.baseAut_over k K σ) := rfl

/-- The endomorphism of a field-extension base change induced by a Galois element,
as `Spec(σ) × id`. -/
def map (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : Gal(K/k)) :
    baseChange k K X ⟶ baseChange k K X :=
  productLift (baseChangeFst k K X ≫ specAut k K σ) (baseChangeSnd k K X)

/-- The Galois-induced base-change map acts as `Spec(σ)` on the `Spec K` factor. -/
theorem map_fst (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : Gal(K/k)) :
    map k K X σ ≫ baseChangeFst k K X = baseChangeFst k K X ≫ specAut k K σ := by
  exact productFst_lift
    (baseChangeFst k K X ≫ specAut k K σ) (baseChangeSnd k K X)

/-- The Galois-induced base-change map acts as the identity on the `X` factor. -/
theorem map_snd (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : Gal(K/k)) :
    map k K X σ ≫ baseChangeSnd k K X = baseChangeSnd k K X := by
  exact productSnd_lift
    (baseChangeFst k K X ≫ specAut k K σ) (baseChangeSnd k K X)

/-- The base-change map attached to the identity Galois automorphism is the identity. -/
theorem map_one (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    map k K X (1 : Gal(K/k)) = 𝟙 _ := sorry

/-- Galois multiplication is transported to categorical composition on the fibre product. -/
theorem map_mul (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ τ : Gal(K/k)) :
    map k K X (σ * τ) = map k K X σ ≫ map k K X τ := sorry

/-- The automorphism of a field-extension base change induced by a Galois element. -/
def aut (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : Gal(K/k)) :
    Aut (baseChange k K X) :=
  { hom := map k K X σ
    inv := map k K X σ.symm
    hom_inv_id := by
      change map k K X σ ≫ map k K X σ⁻¹ = 𝟙 _
      rw [← map_mul, mul_inv_cancel, map_one]
    inv_hom_id := by
      change map k K X σ⁻¹ ≫ map k K X σ = 𝟙 _
      rw [← map_mul, inv_mul_cancel, map_one] }

/-- The hom component of the Galois base-change automorphism is the induced base-change map. -/
theorem aut_hom (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : Gal(K/k)) :
    (aut k K X σ).hom = map k K X σ := rfl

/-- The inverse component of the Galois base-change automorphism is induced by `σ.symm`. -/
theorem aut_inv (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : Gal(K/k)) :
    (aut k K X σ).inv = map k K X σ.symm := rfl

/-- The Galois base-change automorphism at one is the identity automorphism. -/
theorem aut_one (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    aut k K X (1 : Gal(K/k)) = 1 := by
  apply Aut.ext
  exact map_one k K X

/-- The Galois base-change automorphisms are anti-multiplicative in `Aut`, whose multiplication
uses reversed categorical composition. -/
theorem aut_mul (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ τ : Gal(K/k)) :
    aut k K X (σ * τ) = aut k K X τ * aut k K X σ := by
  apply Aut.ext
  exact map_mul k K X σ τ

/-- The opposite Galois group acts by a monoid homomorphism on the automorphisms of the
field-extension base change of an algebraic space. -/
def opAutHom (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    (Gal(K/k))ᵐᵒᵖ →* Aut (baseChange k K X) where
  toFun σ := aut k K X σ.unop
  map_one' := aut_one k K X
  map_mul' σ τ := aut_mul k K X τ.unop σ.unop

/-- The opposite-Galois automorphism hom evaluates to the automorphism induced by the underlying
Galois element. -/
theorem opAutHom_apply (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (σ : (Gal(K/k))ᵐᵒᵖ) :
    opAutHom k K X σ = aut k K X σ.unop := rfl

end Galois

end AlgebraicGeometry.AlgebraicSpace.FieldExtension
