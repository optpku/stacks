module

public import stacks_project.Chap108.Lemma_108_5_10_Hilbert
public import stacks_project.Chap108.Lemma_108_5_10_Tensor

/-!
# Lemma 108.5.10

Tensoring with an invertible `𝒪_X`-module identifies the Grothendieck Quot
functors `Quot_{F/X/B}` and `Quot_{F ⊗ L / X/B}`, and matches the Hilbert
polynomial loci `Quot^P` and `Quot^{P'}` for `P'(t) = P(t + 1)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory Opposite


universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.5.10 (1): let `f : X ⟶ B` be separated and of finite presentation
and let `F` be a quasi-coherent `𝒪_X`-module. Let `L` be an invertible
`𝒪_X`-module. Tensoring with `L` defines an isomorphism
`Quot_{F/X/B} ⟶ Quot_{F ⊗ L / X/B}` of functors of points. -/
@[stacks 0DP7]
def tensorIso (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] :
    quot f F ≅ quot f (F ⊗ L) where
  hom := tensorHom f F L
  inv := tensorInvHom f F L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `tensorIso` is `tensorHom`. -/
theorem tensorIso_hom (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] :
    (tensorIso f F L).hom = tensorHom f F L :=
  sorry

/-- The inverse morphism of `tensorIso` is `tensorInvHom`. -/
theorem tensorIso_inv (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] :
    (tensorIso f F L).inv = tensorInvHom f F L :=
  sorry

/-- The component of `tensorIso` at a test scheme is the setoid quotient map of
`QuotPoint.tensor`. -/
theorem tensorIso_app (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (σ : (SchemesOver B)ᵒᵖ) :
    (tensorIso f F L).hom.app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.tensor L)
          (tensor_rel f F L σ.unop)) :=
  sorry

/-- Lemma 108.5.10 (2): given a numerical polynomial `P`, and writing
`P' = shiftPolynomial P` so that `P'(t) = P(t + 1)`, tensoring with `L` induces
an isomorphism `Quot^P_{F/X/B} ⟶ Quot^{P'}_{F ⊗ L / X/B}` of open and closed
loci of the Quot functors. -/
@[stacks 0DP7]
def tensorIso_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) :
    (quotHilbert f F L P).toFunctor ≅
      (quotHilbert f (F ⊗ L) L (shiftPolynomial P)).toFunctor where
  hom := tensorHom_hilbert f F L P
  inv := tensorInvHom_hilbert f F L P
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `tensorIso_hilbert` is `tensorHom_hilbert`. -/
theorem tensorIso_hilbert_hom (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) :
    (tensorIso_hilbert f F L P hP).hom = tensorHom_hilbert f F L P :=
  sorry

/-- The inverse morphism of `tensorIso_hilbert` is `tensorInvHom_hilbert`. -/
theorem tensorIso_hilbert_inv (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) :
    (tensorIso_hilbert f F L P hP).inv = tensorInvHom_hilbert f F L P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
