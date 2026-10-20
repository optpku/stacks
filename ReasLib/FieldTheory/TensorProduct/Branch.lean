module

public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.LocalRing.Product
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Field branches of tensor-product base changes

A tensor product of field extensions need not be a field.  Its reduction and the residue fields
at maximal ideals are nevertheless canonical, and a further scalar extension can be tested on
each such branch.  This file owns that construction independently of any ramification theory.

@stack 09F4
@stack 09EM
-/

open scoped TensorProduct

universe u v w u'

namespace FieldExtension.TensorProduct

/-- The raw tensor-product base change of `L` along the field extension `K₁ / K`. -/
@[stacks 09F4 "tensor-product field base change"]
abbrev baseChange
    (K : Type u) (L : Type v) (K1 : Type u')
    [Field K] [Field L] [Field K1]
    [Algebra K L] [Algebra K K1] : Type (max v u') :=
  L ⊗[K] K1

/-- The iterated tensor-product extension of `M` after the base change `L ⊗[K] K₁`. -/
@[stacks 09F4 "iterated tensor-product field extension"]
abbrev composite
    (K : Type u) (L : Type v) (M : Type w) (K1 : Type u')
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M] : Type (max w v u') :=
  M ⊗[L] baseChange K L K1

/-- The functorial map from the base change of `L` to the base change of `M` for a tower
`K ⟶ L ⟶ M`.  It applies `L ⟶ M` on the left tensor factor and fixes `K₁` on the
right tensor factor. -/
@[stacks 09EY "map between direct tensor-product base changes"]
def baseChangeMap
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K M] [Algebra K K1] [Algebra L M]
    [IsScalarTower K L M] :
    baseChange K L K1 →ₐ[L] baseChange K M K1 :=
  Algebra.TensorProduct.map (Algebra.ofId L M) (AlgHom.id K K1)

/-- The direct base-change map sends `l ⊗ k₁` to the image of `l` tensored with `k₁`. -/
@[simp, stacks 09EY "direct tensor-product base-change map on pure tensors"]
theorem baseChangeMap_tmul
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K M] [Algebra K K1] [Algebra L M]
    [IsScalarTower K L M] (l : L) (x : K1) :
    baseChangeMap (K := K) (L := L) (M := M) (K1 := K1) (l ⊗ₜ[K] x) =
      algebraMap L M l ⊗ₜ[K] x := sorry

/-- The canonical equivalence from the iterated base change
`M ⊗[L] (L ⊗[K] K₁)` to the direct base change `M ⊗[K] K₁`. -/
@[stacks 09F4 "iterated-to-direct tensor base change", stacks 09EY
  "iterated-to-direct tensor base change"]
noncomputable def compositeEquivBaseChange
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K M] [Algebra K K1] [Algebra L M]
    [IsScalarTower K L M] :
    composite K L M K1 ≃ₐ[L] M ⊗[K] K1 :=
  Algebra.TensorProduct.cancelBaseChange K L L M K1

/-- The iterated-to-direct equivalence multiplies the middle scalar into the left tensor factor. -/
@[simp, stacks 09F4 "iterated-to-direct tensor application", stacks 09EY
  "iterated-to-direct tensor application"]
theorem compositeEquivBaseChange_tmul
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K M] [Algebra K K1] [Algebra L M]
    [IsScalarTower K L M] (m : M) (l : L) (x : K1) :
    compositeEquivBaseChange (K := K) (L := L) (M := M) (K1 := K1)
        (m ⊗ₜ[L] (l ⊗ₜ[K] x)) = (l • m) ⊗ₜ[K] x := sorry

/-- The iterated tensor product is a field exactly when the direct tensor product is a field. -/
@[stacks 09F4 "iterated tensor field criterion", stacks 09EY
  "iterated tensor field criterion"]
theorem composite_isField_iff
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K M] [Algebra K K1] [Algebra L M]
    [IsScalarTower K L M] :
    IsField (composite K L M K1) ↔ IsField (M ⊗[K] K1) := sorry

/-- The reduced tensor product of two field extensions of the same base field. -/
@[stacks 09F4 "reduced tensor-product base change"]
abbrev reduced
    (K : Type u) (L : Type v) (K1 : Type u')
    [Field K] [Field L] [Field K1]
    [Algebra K L] [Algebra K K1] : Type (max v u') :=
  baseChange K L K1 ⧸ nilradical (baseChange K L K1)

section FiniteReduced

variable {K : Type u} {L : Type v} {K1 : Type u'}
variable [Field K] [Field L] [Field K1] [Algebra K L] [Algebra K K1]

/-- The reduced tensor product is nontrivial when one field factor is finite over the base. -/
@[stacks 09EM "nontrivial finite reduced tensor product"]
theorem reduced_nontrivial [FiniteDimensional K K1] :
    Nontrivial (reduced K L K1) := sorry

/-- A finite field factor makes the reduced tensor product finite-dimensional over the other
factor. -/
@[stacks 09EM "finite-dimensional reduced tensor product"]
theorem reduced_finiteDimensional [FiniteDimensional K K1] :
    FiniteDimensional L (reduced K L K1) := sorry

/-- The reduced tensor product with a finite field factor admits a finite ring-product
decomposition. -/
@[stacks 09EM "finite decomposition of a reduced tensor product"]
theorem reduced_isFiniteProduct [FiniteDimensional K K1] :
    RingProduct.isFiniteProduct (reduced K L K1) := sorry

/-- Every maximal localization of the finite reduced tensor product is a field. -/
@[stacks 09EM "field branches of a finite reduced tensor product"]
theorem reduced_localization_isField [FiniteDimensional K K1]
    (p : Ideal (reduced K L K1)) [p.IsMaximal] :
    IsField (Localization.AtPrime p) := sorry

/-- The finite reduced tensor product has a finite algebra-product presentation by finite field
extensions of the other factor. -/
@[stacks 09EM "finite product of fields for a reduced tensor product"]
theorem reduced_finiteProductOfFields [FiniteDimensional K K1] :
    ∃ D : AlgProduct.Decomposition.Finite L (reduced K L K1),
      Nonempty D.index ∧
        ∀ i, IsField (D.factor i) ∧ FiniteDimensional L (D.factor i) := sorry

/-- Remark 15.115.1 (7): if the finite factor is separable, the reduced tensor product has a
nonempty finite algebra-product presentation by finite separable field extensions of `L`. -/
@[stacks 09EM "Remark 15.115.1 (7), finite product of finite separable fields"]
theorem reduced_finiteProductOfSeparableFields [FiniteDimensional K K1]
    [Algebra.IsSeparable K K1] :
    ∃ D : AlgProduct.Decomposition.Finite L (reduced K L K1),
      Nonempty D.index ∧
        ∀ i, IsField (D.factor i) ∧ FiniteDimensional L (D.factor i) ∧
          Algebra.IsSeparable L (D.factor i) := sorry

/-- Quotienting a commutative ring by its nilradical produces a reduced ring. -/
@[stacks 09EM "reducedness of the reduced tensor product"]
theorem reduced_isReduced : IsReduced (reduced K L K1) := sorry

/-- If the finite field factor is separable, the canonical quotient from the raw tensor product
to its reduction is bijective. -/
@[stacks 09EM "separable tensor product quotient is bijective"]
theorem quotient_bijective_of_finite_separable [FiniteDimensional K K1]
    [Algebra.IsSeparable K K1] :
    Function.Bijective
      (Ideal.Quotient.mkₐ L (nilradical (baseChange K L K1))) := sorry

/-- The raw tensor product is canonically equivalent to its reduction when the finite factor is
separable. -/
@[stacks 09EM "separable tensor product equivalence with its reduction"]
noncomputable def tensorEquivReduced [FiniteDimensional K K1]
    [Algebra.IsSeparable K K1] :
    baseChange K L K1 ≃ₐ[L] reduced K L K1 :=
  AlgEquiv.ofBijective
    (Ideal.Quotient.mkₐ L (nilradical (baseChange K L K1)))
    quotient_bijective_of_finite_separable

/-- The separable tensor-product equivalence is the canonical quotient map on elements. -/
@[simp, stacks 09EM "separable tensor product equivalence application"]
theorem tensorEquivReduced_apply [FiniteDimensional K K1]
    [Algebra.IsSeparable K K1] (x : baseChange K L K1) :
    tensorEquivReduced (K := K) (L := L) (K1 := K1) x =
      Ideal.Quotient.mkₐ L (nilradical (baseChange K L K1)) x := sorry

end FiniteReduced

/-- A maximal reduced tensor-product branch on which the induced scalar extension of `M` is a
field. -/
@[stacks 09F4 "field branch of a tensor-product base change"]
structure Branch
    (K : Type u) (L : Type v) (M : Type w) (K1 : Type u')
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M] where
  /-- The selected maximal point of the reduced base change. -/
  m : MaximalSpectrum (reduced K L K1)
  /-- The extension of `M` to the residue field of the selected branch is a field. -/
  isField : IsField (M ⊗[L] m.ResidueField)

namespace Branch

/-- The residue field selected by a tensor-product branch. -/
@[stacks 09F4 "residue field selected by a tensor-product branch"]
abbrev field
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    (b : Branch K L M K1) : Type (max v u') :=
  b.m.ResidueField

/-- The scalar extension of `M` along the residue field selected by a branch. -/
@[stacks 09F4 "field extension selected by a tensor-product branch"]
abbrev extension
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    (b : Branch K L M K1) : Type (max w v u') :=
  M ⊗[L] b.field

/-- The field structure selected by a branch.  This is a named ordinary definition rather than a
global instance because a tensor product can carry competing left- and right-oriented actions. -/
@[reducible, stacks 09F4 "field structure selected by a tensor-product branch"]
noncomputable def fieldStructure
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    (b : Branch K L M K1) : Field b.extension :=
  b.isField.toField

/-- The quotient presentation of a maximal branch is canonically equivalent to its residue-field
presentation. -/
@[stacks 09F4 "quotient presentation of a tensor-product branch"]
noncomputable def quotientFieldEquiv
    {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
    [Field K] [Field L] [Field M] [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    (b : Branch K L M K1) :
    (reduced K L K1 ⧸ b.m.asIdeal) ≃ₐ[L] b.field :=
  Ideal.ResidueField.quotientAlgEquiv (K := L) b.m.asIdeal

end Branch

end FieldExtension.TensorProduct
