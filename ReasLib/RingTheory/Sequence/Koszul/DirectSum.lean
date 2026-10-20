/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Distributive.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import ReasLib.RingTheory.Sequence.Koszul.Family
public import ReasLib.RingTheory.Sequence.Koszul.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes of direct sums

The Koszul complex of a coproduct linear form is the tensor product of the two Koszul complexes.
The comparison is built from explicit maps on exterior powers in both directions.  Finite-family
concatenation is exposed as a specialization through the canonical coordinate equivalence.

@stack 0664
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex MonoidalCategory
open scoped KoszulComplex

namespace KoszulComplex

variable {R : Type u} [CommRing R]
variable {E E' : Type u} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']

namespace DirectSum

/-- The contribution with left exterior degree `p` to the degree-`n` map from the Koszul
complex of a coproduct linear form to the tensor product complex. -/
@[stacks 0664 "summand of the direct-sum Koszul comparison"]
noncomputable def forwardSummand
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) (p : Fin (n + 1)) :
    _root_.AlternatingMap R (ModuleCat.of R (E × E'))
      ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n) (Fin n) :=
  let q : ℕ := n - p
  let hpq : (p : ℕ) + q = n := Nat.add_sub_of_le p.is_le
  let left : (E × E') [⋀^Fin p]→ₗ[R] ⋀[R]^p E :=
    (exteriorPower.ιMulti R p).compLinearMap (LinearMap.fst R E E')
  let right : (E × E') [⋀^Fin q]→ₗ[R] ⋀[R]^q E' :=
    (exteriorPower.ιMulti R q).compLinearMap (LinearMap.snd R E E')
  let alternating :
      _root_.AlternatingMap R (ModuleCat.of R (E × E'))
        ((((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R)) (Fin n) :=
    (left.domCoprod right).domDomCongr (finSumFinEquiv.trans (finCongr hpq))
  let inclusion :
      ((((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q) : ModuleCat R)) ⟶
        (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
    HomologicalComplex.ιTensorObj (koszulComplex φ) (koszulComplex ψ) p q n hpq
  inclusion.hom.compAlternatingMap alternating

/-- The degree-`n` forward map from the Koszul complex of a coproduct linear form to the
totalized tensor product. -/
@[stacks 0664 "forward direct-sum Koszul comparison"]
noncomputable def forwardComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ⟶
      (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
  ModuleCat.ofHom <|
    exteriorPower.alternatingMapLinearEquiv
      (∑ p : Fin (n + 1), forwardSummand φ ψ n p)

/-- Ambient exterior-algebra multiplication defining the reverse map on a `(p,q)` tensor
summand. -/
@[stacks 0664 "ambient reverse direct-sum Koszul comparison"]
noncomputable def reverseAmbient (p q : ℕ) :
    TensorProduct R (⋀[R]^p E) (⋀[R]^q E') →ₗ[R] ExteriorAlgebra R (E × E') :=
  let left : ⋀[R]^p E →ₗ[R] ExteriorAlgebra R (E × E') :=
    (ExteriorAlgebra.map (LinearMap.inl R E E')).toLinearMap.comp (Submodule.subtype _)
  let right : ⋀[R]^q E' →ₗ[R] ExteriorAlgebra R (E × E') :=
    (ExteriorAlgebra.map (LinearMap.inr R E E')).toLinearMap.comp (Submodule.subtype _)
  (LinearMap.mul' R (ExteriorAlgebra R (E × E'))).comp (TensorProduct.map left right)

/-- Ambient reverse multiplication lands in exterior degree `p + q`. -/
theorem reverseAmbient_mem (p q : ℕ)
    (z : TensorProduct R (⋀[R]^p E) (⋀[R]^q E')) :
    reverseAmbient (R := R) (E := E) (E' := E') p q z ∈ ⋀[R]^(p + q) (E × E') := sorry

/-- The explicit reverse map from the `(p,q)` tensor summand to exterior degree `p + q`. -/
@[stacks 0664 "reverse summand of the direct-sum Koszul comparison"]
noncomputable def reverseSummand
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q : ℕ) :
    (((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q : ModuleCat R)) ⟶
      (koszulComplex (φ.coprod ψ)).X (p + q) :=
  ModuleCat.ofHom <|
    LinearMap.codRestrict (⋀[R]^(p + q) (E × E'))
      (reverseAmbient (R := R) (E := E) (E' := E') p q)
      (reverseAmbient_mem (R := R) (E := E) (E' := E') p q)

/-- The reverse `(p,q)` summand transported to a specified total degree `n`. -/
@[stacks 0664 "reverse Koszul summand in a specified total degree"]
noncomputable def reverseSummandTo
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (p q n : ℕ) (h : p + q = n) :
    (((koszulComplex φ).X p) ⊗ ((koszulComplex ψ).X q : ModuleCat R)) ⟶
      (koszulComplex (φ.coprod ψ)).X n :=
  h ▸ reverseSummand φ ψ p q

/-- The degree-`n` reverse map, descended from multiplication on every tensor summand. -/
@[stacks 0664 "reverse direct-sum Koszul comparison"]
noncomputable def reverseComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n ⟶
      (koszulComplex (φ.coprod ψ)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := koszulComplex φ) (K₂ := koszulComplex ψ)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.down ℕ)
    (fun p q h ↦ reverseSummandTo φ ψ p q n h)

/-- The forward components commute with the Koszul and tensor-product differentials. -/
theorem forwardComponent_commSq
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    CommSq
      (forwardComponent φ ψ i)
      ((koszulComplex (φ.coprod ψ)).d i j)
      ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).d i j)
      (forwardComponent φ ψ j) := sorry

/-- In each degree, the forward map followed by explicit exterior multiplication is the
identity. -/
theorem forwardComponent_reverseComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    forwardComponent φ ψ n ≫ reverseComponent φ ψ n =
      𝟙 ((koszulComplex (φ.coprod ψ)).X n) := sorry

/-- In each degree, explicit exterior multiplication followed by the forward map is the
identity. -/
theorem reverseComponent_forwardComponent
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    reverseComponent φ ψ n ≫ forwardComponent φ ψ n =
      𝟙 ((HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n) := sorry

/-- The explicit degreewise isomorphism between the coproduct Koszul term and the corresponding
term of the tensor-product totalization. -/
@[stacks 0664 "degreewise direct-sum Koszul isomorphism"]
noncomputable def componentIso
    (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) (n : ℕ) :
    (koszulComplex (φ.coprod ψ)).X n ≅
      (HomologicalComplex.tensorObj (koszulComplex φ) (koszulComplex ψ)).X n :=
  CategoryTheory.Iso.mk (forwardComponent φ ψ n) (reverseComponent φ ψ n)
    (forwardComponent_reverseComponent φ ψ n)
    (reverseComponent_forwardComponent φ ψ n)

/-- The Koszul complex of a coproduct linear form is canonically isomorphic to the tensor
product of the two Koszul complexes. -/
@[stacks 0664 "direct-sum Koszul tensor comparison"]
noncomputable def isoTensor (φ : E →ₗ[R] R) (ψ : E' →ₗ[R] R) :
    koszulComplex (φ.coprod ψ) ≅ koszulComplex φ ⊗ koszulComplex ψ :=
  Hom.isoOfComponents (componentIso φ ψ)
    (fun i j hij ↦ (forwardComponent_commSq φ ψ i j hij).w)

end DirectSum

namespace Family

/-- The canonical coordinate equivalence sending a pair of finite vectors to their
concatenation. -/
@[stacks 0664 "coordinate equivalence for appended Koszul families"]
noncomputable def appendLinearEquiv (r s : ℕ) :
    ((Fin r → R) × (Fin s → R)) ≃ₗ[R] (Fin (r + s) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) R R).symm ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun _ : Fin r ⊕ Fin s ↦ R) finSumFinEquiv

/-- The coordinate equivalence evaluates as `Fin.append`. -/
@[simp]
theorem appendLinearEquiv_apply {r s : ℕ}
    (x : (Fin r → R) × (Fin s → R)) :
    appendLinearEquiv r s x = Fin.append x.1 x.2 := sorry

/-- Splitting an appended-family linear form recovers the coproduct of its two linear forms. -/
theorem linearForm_append_comp_symm {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    ((koszulLinearForm f).coprod (koszulLinearForm g)).comp
        (appendLinearEquiv r s).symm.toLinearMap =
      koszulLinearForm (Fin.append f g) := sorry

/-- Concatenating coordinates carries the appended-family linear form to the coproduct linear
form. -/
theorem linearForm_append_comp {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    (koszulLinearForm (Fin.append f g)).comp (appendLinearEquiv r s).toLinearMap =
      (koszulLinearForm f).coprod (koszulLinearForm g) := sorry

/-- The forward Koszul map from an appended family to its coproduct presentation. -/
@[stacks 0664 "forward appended-family Koszul comparison"]
noncomputable def appendCoprodHom {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    family (Fin.append f g) ⟶
      koszulComplex ((koszulLinearForm f).coprod (koszulLinearForm g)) :=
  KoszulComplex.map (appendLinearEquiv r s).symm.toLinearMap
    (linearForm_append_comp_symm f g)

/-- The inverse Koszul map from the coproduct presentation to the appended family. -/
@[stacks 0664 "inverse appended-family Koszul comparison"]
noncomputable def appendCoprodInv {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    koszulComplex ((koszulLinearForm f).coprod (koszulLinearForm g)) ⟶
      family (Fin.append f g) :=
  KoszulComplex.map (appendLinearEquiv r s).toLinearMap (linearForm_append_comp f g)

/-- The appended-family map followed by its explicit inverse is the identity. -/
theorem appendCoprodHom_inv_id {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    appendCoprodHom f g ≫ appendCoprodInv f g = 𝟙 (family (Fin.append f g)) := sorry

/-- The inverse appended-family map followed by the forward map is the identity. -/
theorem appendCoprodInv_hom_id {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    appendCoprodInv f g ≫ appendCoprodHom f g =
      𝟙 (koszulComplex ((koszulLinearForm f).coprod (koszulLinearForm g))) := sorry

/-- The Koszul complex of an appended family is canonically isomorphic to the coproduct-linear
form presentation. -/
@[stacks 0664 "appended-family Koszul coproduct isomorphism"]
noncomputable def appendCoprodIso {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    family (Fin.append f g) ≅
      koszulComplex ((koszulLinearForm f).coprod (koszulLinearForm g)) :=
  CategoryTheory.Iso.mk (appendCoprodHom f g) (appendCoprodInv f g)
    (appendCoprodHom_inv_id f g) (appendCoprodInv_hom_id f g)

/-- Lemma 15.28.12: the Koszul complex on `Fin.append f g` is canonically isomorphic to the
tensor product of the Koszul complexes on `f` and `g`. -/
@[stacks 0664 "Lemma 15.28.12"]
noncomputable def appendIsoTensor {r s : ℕ}
    (f : Fin r → R) (g : Fin s → R) :
    K•(Fin.append f g) ≅ K•(f) ⊗ K•(g) :=
  appendCoprodIso f g ≪≫ DirectSum.isoTensor (koszulLinearForm f) (koszulLinearForm g)

end Family
end KoszulComplex
