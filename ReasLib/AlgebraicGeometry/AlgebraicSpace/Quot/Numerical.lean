/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.CohStack
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TensorPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Numerical loci of the Quot functor -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite

-- Local declaration justification (metaprogramming implementation): Exposed categorical data uses private concrete maps and named proof laws, which Lean's module visibility requires exporting internally.
set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Numerical invariants agree for quotient representatives with the same kernel. -/
theorem QuotPoint.hasNumerical_iff_of_rel {f : X ⟶ B} {F : X.Modules}
    {σ : SchemeOver B} [FinitePresentation f] {I : Type u}
    (Q₁ Q₂ : QuotPoint f F σ) (h : Rel Q₁.point Q₂.point)
    (E : I → ModuleDerived X) (P : I → ℤ) :
    Q₁.toCohStack.HasNumerical E P ↔ Q₂.toCohStack.HasNumerical E P := sorry

/-- Base change preserves the existence of a representative with prescribed numerical invariants. -/
private theorem quotNumerical_map_mem (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) (q : (quot f F).obj σ) :
    (∃ Q : QuotPoint f F σ.unop,
      _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧ Q.toCohStack.HasNumerical E P) →
    ∃ Q : QuotPoint f F τ.unop,
      _root_.Quotient.mk (quotSetoid f F τ.unop) Q = (quot f F).map h q ∧
        Q.toCohStack.HasNumerical E P := sorry

/-- The numerical locus `Quot^P_{F/X/B}` inside `Quot_{F/X/B}`, as the subfunctor
of kernel-identified classes whose forgotten sheaf has numerical invariants `P`
with respect to a family of perfect derived modules `E`. -/
def quotNumerical (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Subfunctor (quot f F) where
  obj σ :=
    setOf fun q ↦
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.toCohStack.HasNumerical E P
  map := quotNumerical_map_mem f F E P hE

/-- A class lies in `quotNumerical` if and only if some representing Quot-point
has numerical invariants `P` with respect to `E`. -/
theorem mem_quotNumerical (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) {σ : (SchemeOver B)ᵒᵖ}
    (q : (quot f F).obj σ) :
    q ∈ (quotNumerical f F E P hE).obj σ ↔
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.toCohStack.HasNumerical E P := sorry

/-- The inclusion of the numerical locus into the ambient Quot functor. -/
def quotNumericalι (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (quotNumerical f F E P hE).toFunctor ⟶ quot f F :=
  (quotNumerical f F E P hE).ι

/-- `quotNumericalι` is the subfunctor inclusion of `quotNumerical`. -/
theorem quotNumericalι_eq (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    quotNumericalι f F E P hE = (quotNumerical f F E P hE).ι := sorry

/-- The derived family `n ↦ L^{⊗ n}` on `ULift ℤ`. -/
def invertiblePowerFamily (L : X.Modules) [isInvertibleObject L] :
    ULift.{u, 0} ℤ → ModuleDerived X :=
  fun n ↦ ModuleDerived.tensorPowerInt
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) n.down

/-- Evaluating `invertiblePowerFamily L` at `⟨n⟩` recovers the integral derived
tensor power of `L[0]`. -/
theorem invertiblePowerFamily_apply (L : X.Modules) [isInvertibleObject L]
    (n : ℤ) :
    invertiblePowerFamily L (⟨n⟩ : ULift.{u, 0} ℤ) =
      ModuleDerived.tensorPowerInt
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) n := sorry

/-- Integral derived tensor powers of an invertible `𝒪_X`-module remain perfect. -/
theorem isPerfect_invertiblePowerFamily (L : X.Modules) [isInvertibleObject L]
    (n : ULift.{u, 0} ℤ) :
    ModuleDerived.IsPerfect (invertiblePowerFamily L n) := sorry

/-- The Hilbert numerical locus `Quot^{P,L}_{F/X/B}` of the family
`n ↦ L^{⊗ n}`. -/
abbrev quotNumericalHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :=
  quotNumerical f F (invertiblePowerFamily L) (fun n ↦ P n.down)
    (isPerfect_invertiblePowerFamily L)

/-- `quotNumericalHilbert` is `quotNumerical` of `invertiblePowerFamily L`. -/
theorem quotNumericalHilbert_eq (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) :
    quotNumericalHilbert f F L P =
      quotNumerical f F (invertiblePowerFamily L) (fun n ↦ P n.down)
        (isPerfect_invertiblePowerFamily L) := sorry

/-- Membership of the class of any representative is its target's numerical condition. -/
theorem mem_quotNumerical_mk (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    (σ : SchemeOver B) (Q : QuotPoint f F σ) :
    _root_.Quotient.mk (quotSetoid f F σ) Q ∈ (quotNumerical f F E P hE).obj (op σ) ↔
      Q.toCohStack.HasNumerical E P := sorry

/-- The forgetful image of a numerical quotient has the prescribed numerical invariants. -/
theorem quotNumericalToCoh_mem (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    (a : (quotNumerical f F E P hE).toFunctor.Elementsᵒᵖ) :
    CohStack.numerical f E P
      (((CategoryOfElements.map (quotNumericalι f F E P hE)).op ⋙ forgetCoh f F).obj a) := sorry

/-- The forgetful functor restricted to the numerical quotient locus. -/
def quotNumericalToCoh (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (quotNumerical f F E P hE).toFunctor.Elementsᵒᵖ ⥤ CohStack.Numerical f E P :=
  (CohStack.numerical f E P).lift
    ((CategoryOfElements.map (quotNumericalι f F E P hE)).op ⋙ forgetCoh f F)
    (quotNumericalToCoh_mem f F E P hE)

/-- Restricting the forgetful functor retains its underlying functor and projection to test schemes. -/
theorem quotNumericalToCoh_spec (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    quotNumericalToCoh f F E P hE ⋙ (CohStack.numerical f E P).ι =
        (CategoryOfElements.map (quotNumericalι f F E P hE)).op ⋙ forgetCoh f F ∧
      (quotNumericalToCoh f F E P hE ⋙ (CohStack.numerical f E P).ι) ⋙ CohStack.p f =
        (CategoryOfElements.π (quotNumerical f F E P hE).toFunctor).leftOp ⋙
          CostructuredArrow.proj (ofOverFunctor S) B := sorry

/-- The numerical Quot locus and its restricted forgetful functor form the
canonical commutative square with the numerical coherent-sheaf inclusion. -/
def quotNumericalSquare (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    CategoricalPullback.CatCommSqOver (forgetCoh f F) (CohStack.numerical f E P).ι
      ((quotNumerical f F E P hE).toFunctor.Elementsᵒᵖ) where
  fst := (CategoryOfElements.map (quotNumericalι f F E P hE)).op
  snd := quotNumericalToCoh f F E P hE
  iso := ((CohStack.numerical f E P).liftCompιIso
    ((CategoryOfElements.map (quotNumericalι f F E P hE)).op ⋙ forgetCoh f F)
    (quotNumericalToCoh_mem f F E P hE)).symm

/-- The numerical Quot square is two-Cartesian: its canonical comparison is an equivalence. -/
instance quotNumericalSquare_comparison_isEquivalence (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (quotNumericalSquare f F E P hE).comparison.IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
