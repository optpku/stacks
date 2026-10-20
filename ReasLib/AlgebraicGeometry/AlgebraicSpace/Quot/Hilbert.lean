module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.FieldFiber
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import ReasLib.RingTheory.Polynomial.Numerical
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Basic

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalCategory.InvertiblePower CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The `n`th tensor twist of the quotient module of a Quot-point by `L_T`. -/
def QuotPoint.twist {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ) : (fiber f σ).Modules :=
  eval (C := (Limits.pullback f σ.hom).Modules)
      ((Modules.pullback (Limits.pullback.fst f σ.hom)).obj L) Q.point.module n

/-- `QuotPoint.twist Q L n` is `InvertiblePower.eval L_T Q n`. -/
theorem QuotPoint.twist_eq {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ) :
    Q.twist L n =
      eval (C := (Limits.pullback f σ.hom).Modules)
        ((Modules.pullback (Limits.pullback.fst f σ.hom)).obj L) Q.point.module n :=
  sorry

/-- The residue-field fibre of a twist: pull `Q ⊗ L_T^{⊗ n}` back to
`X_T ×_T Spec(K)` along a field-valued point of the test scheme. -/
def QuotPoint.twistFiber {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    (Limits.pullback (Limits.pullback.snd f σ.hom) t.hom).Modules :=
  (Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f σ.hom) t.hom)).obj
    (Q.twist L n)

/-- `twistFiber` is module pullback of the twist along the projection to `X_T`. -/
theorem QuotPoint.twistFiber_eq {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    Q.twistFiber L n t =
      (Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f σ.hom) t.hom)).obj
        (Q.twist L n) :=
  sorry

/-- Euler characteristic `χ(X_t, Q_t ⊗ L_t^{⊗ n})` of a twisted Quot-point fibre. -/
def QuotPoint.twistEulerChar {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) : ℤ :=
  fieldFiberEulerChar t.structureHom
    (Limits.pullback.snd (Limits.pullback.snd f σ.hom) t.hom)
    (Q.twistFiber L n t)

/-- `twistEulerChar` is `fieldFiberEulerChar` of the twisted residue-field
fibre. -/
theorem QuotPoint.twistEulerChar_eq {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    Q.twistEulerChar L n t =
      fieldFiberEulerChar t.structureHom
        (Limits.pullback.snd (Limits.pullback.snd f σ.hom) t.hom)
        (Q.twistFiber L n t) :=
  sorry

/-- A Quot-point has Hilbert polynomial `P` with respect to `L` when for every
integer `n` and every field-valued point `t` of the test scheme,
`χ(X_t, Q_t ⊗ L_t^{⊗ n}) = P n`. -/
def QuotPoint.HasHilbertPolynomial {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) : Prop :=
  ∀ (n : ℤ) (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)),
    Q.twistEulerChar L n t = P n

/-- The Hilbert polynomial condition is the fibrewise identity
`χ(X_t, Q_t ⊗ L_t^{⊗ n}) = P n`. -/
theorem QuotPoint.hasHilbertPolynomial_iff {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    Q.HasHilbertPolynomial L P ↔
      ∀ (n : ℤ) (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)),
        Q.twistEulerChar L n t = P n :=
  sorry

/-- A Quot-point has Hilbert polynomial `P` with respect to `L` if and only if the
tensored Quot-point has Hilbert polynomial `fun t ↦ P (t + 1)` with respect to
the same `L`. -/
theorem tensor_hasHilbertPolynomial {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    Q.HasHilbertPolynomial L P ↔
      (Q.tensor L).HasHilbertPolynomial L (fun t ↦ P (t + 1)) :=
  sorry

/-- The Hilbert-polynomial locus `Quot^P_{F/X/B}` inside `Quot_{F/X/B}`, as the
subfunctor of kernel-identified classes admitting a representative with Hilbert
polynomial `P` with respect to `L`. -/
def quotHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    Subfunctor (quot f F) where
  obj σ :=
    setOf fun q ↦
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasHilbertPolynomial L P
  map := sorry

/-- A class lies in `quotHilbert` if and only if some representing Quot-point has
Hilbert polynomial `P` with respect to `L`. -/
theorem mem_quotHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    {σ : (SchemeOver B)ᵒᵖ} (q : (quot f F).obj σ) :
    q ∈ (quotHilbert f F L P).obj σ ↔
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasHilbertPolynomial L P :=
  sorry

/-- The Hilbert-locus inclusion is an open immersion of functors of points. -/
theorem quotHilbertι_isOpenImmersion (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left :
        MorphismProperty (SchemeOver B))
      (quotHilbert f F L P).ι :=
  sorry

/-- The Hilbert-locus inclusion is a closed immersion of functors of points. -/
theorem quotHilbertι_isClosedImmersion (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (fun _ _ h ↦ AlgebraicGeometry.IsClosedImmersion h.left.left :
        MorphismProperty (SchemeOver B))
      (quotHilbert f F L P).ι :=
  sorry

/-- The natural transformation of Hilbert loci induced by tensoring with `L`. -/
def tensorHom_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    (quotHilbert f F L P).toFunctor ⟶
      (quotHilbert f (F ⊗ L) L (fun t ↦ P (t + 1))).toFunctor where
  app σ :=
    TypeCat.ofHom fun x ↦
      ⟨ConcreteCategory.hom ((tensorHom f F L).app σ) x.val, sorry⟩
  naturality := sorry

/-- The inverse natural transformation of Hilbert loci induced by the inverse of
tensoring with `L`. -/
def tensorInvHom_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    (quotHilbert f (F ⊗ L) L (fun t ↦ P (t + 1))).toFunctor ⟶
      (quotHilbert f F L P).toFunctor where
  app σ :=
    TypeCat.ofHom fun x ↦
      ⟨ConcreteCategory.hom ((tensorInvHom f F L).app σ) x.val, sorry⟩
  naturality := sorry

/-- Tensoring Hilbert loci commutes with the inclusions into the ambient Quot
functors. -/
theorem tensorHom_hilbert_comp_ι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) :
    tensorHom_hilbert f F L P ≫ (quotHilbert f (F ⊗ L) L (fun t ↦ P (t + 1))).ι =
      (quotHilbert f F L P).ι ≫ tensorHom f F L :=
  sorry

/-- Tensoring quotients with an invertible module identifies the Hilbert loci for
polynomials related by the shift of the integer argument by one. -/
def tensorIso_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) :
    (quotHilbert f F L P).toFunctor ≅
      (quotHilbert f (F ⊗ L) L (fun t ↦ P (t + 1))).toFunctor where
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
