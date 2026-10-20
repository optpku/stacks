module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType.Noetherian
public import ReasLib.RingTheory.AdicCompletion.Polynomial.Evaluation
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

/-!
# Completed presentations induced by finite-type polynomial presentations

Given a surjective presentation `α : A[x_ι] → B` of a finite-type algebra over a
Noetherian ring, completed evaluation induces a polynomial presentation of
the `I`-adic completion `B^∧`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
variable {ι : Type u}

/-- The `I`-adic completion `B^∧` of a finite-type `A`-algebra, taken along the
extended ideal `I B`. -/
abbrev algebraCompletion (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Type u :=
  AdicCompletion (I.map (algebraMap A B)) B

/-- Unfolding of `algebraCompletion I B` as the adic completion of `B` along `I B`. -/
theorem algebraCompletion_eq (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    algebraCompletion I B = AdicCompletion (I.map (algebraMap A B)) B :=
  rfl

/-- The algebra map `A → B^∧` factors through `B`. -/
instance instAlgebraCompletion_isScalarTower (I : Ideal A) :
    IsScalarTower A B (algebraCompletion I B) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Completeness of `B^∧` along the extended ideal `I · B^∧`, so that completed
evaluation into `B^∧` is defined. -/
instance instAlgebraCompletion_isAdicComplete (I : Ideal A) :
    IsAdicComplete (I.map (algebraMap A (algebraCompletion I B))) (algebraCompletion I B) :=
  (IsAdicComplete.map_algebraMap_iff (R := A) (S := algebraCompletion I B)
      (M := algebraCompletion I B) I).mpr inferInstance

/-- The dense map `A[x_ι] → A[x_ι]^∧` is an `A`-algebra homomorphism. -/
instance instPolynomialCompletion_isScalarTower (I : Ideal A) :
    IsScalarTower A (MvPolynomial ι A) (polynomialCompletion A I ι) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl


/-- The ordinary polynomial presentation of `B` over `A` associated with a
chosen surjection `α : A[x_ι] → B`. -/
abbrev polynomialExtension (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) :
    Algebra.Extension A B :=
  (Algebra.Generators.ofAlgHom α hα).toExtension

/-- The kernel of `polynomialExtension α hα` is the kernel of `α`. -/
theorem polynomialExtension_ker (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) :
    (polynomialExtension α hα).ker = RingHom.ker α :=
  sorry

/-- The dense `A`-algebra map `A[x_ι] → A[x_ι]^∧`. -/
def polynomialToCompletionAlgHom (I : Ideal A) :
    MvPolynomial ι A →ₐ[A] polynomialCompletion A I ι :=
  IsScalarTower.toAlgHom A (MvPolynomial ι A) (polynomialCompletion A I ι)

/-- The dense map sends a polynomial to its image in the completed polynomial ring. -/
theorem polynomialToCompletionAlgHom_apply (I : Ideal A) (p : MvPolynomial ι A) :
    polynomialToCompletionAlgHom I p =
      AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p :=
  sorry

variable (I : Ideal A)

/-- The continuous `A`-algebra map `A[x_ι]^∧ → B^∧` extending `α`, obtained by
completed evaluation at the images of the variables in `B^∧`. -/
def completionAlgHom (α : MvPolynomial ι A →ₐ[A] B) :
    polynomialCompletion A I ι →ₐ[A] algebraCompletion I B :=
  adicAeval I fun i ↦ algebraMap B (algebraCompletion I B) (α (MvPolynomial.X i))

/-- Completed evaluation sends the indeterminate `X I i` to the image of
`α (MvPolynomial.X i)` in `B^∧`. -/
theorem completionAlgHom_X (α : MvPolynomial ι A →ₐ[A] B) (i : ι) :
    completionAlgHom I α (X I i) =
      algebraMap B (algebraCompletion I B) (α (MvPolynomial.X i)) :=
  sorry

/-- The completed map extends `α` along the dense map from `A[x_ι]`. -/
theorem completionAlgHom_comp_of (α : MvPolynomial ι A →ₐ[A] B) (p : MvPolynomial ι A) :
    completionAlgHom I α
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) =
      algebraMap B (algebraCompletion I B) (α p) :=
  sorry

/-- The completed structure map induced by `α` is surjective. -/
theorem completionAlgHom_surjective (α : MvPolynomial ι A →ₐ[A] B)
    (hα : Function.Surjective α) :
    Function.Surjective (completionAlgHom I α) :=
  sorry

/-- The completed polynomial presentation of `B^∧` induced by a chosen
presentation `α : A[x_ι] → B`. -/
def completionPresentation (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) :
    Presentation A (algebraCompletion I B) I ι :=
  Presentation.ofSurjective (completionAlgHom I α) (completionAlgHom_surjective I α hα)

/-- The structure map of the completed presentation is `completionAlgHom`. -/
theorem completionPresentation_toAlgHom (α : MvPolynomial ι A →ₐ[A] B)
    (hα : Function.Surjective α) :
    (completionPresentation I α hα).toAlgHom = completionAlgHom I α :=
  rfl

/-- The canonical polynomial completion map respects the coefficient maps. -/
private theorem polynomialToCompletionHom_toRingHom_algebraMap
    (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) (a : A) :
    (polynomialToCompletionAlgHom I).toRingHom
        (algebraMap A (polynomialExtension α hα).Ring a) =
      algebraMap A (completionPresentation I α hα).toExtension.Ring
        (algebraMap A A a) :=
  sorry

/-- The polynomial completion map commutes with the structure maps to the algebra
and its completion. -/
private theorem polynomialToCompletionHom_algebraMap_toRingHom
    (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α)
    (p : (polynomialExtension α hα).Ring) :
    algebraMap (completionPresentation I α hα).toExtension.Ring (algebraCompletion I B)
        ((polynomialToCompletionAlgHom I).toRingHom p) =
      algebraMap B (algebraCompletion I B)
        (algebraMap (polynomialExtension α hα).Ring B p) :=
  sorry

/-- The morphism of `A`-extensions from the ordinary polynomial presentation of
`B` to the completed presentation of its adic completion. -/
@[no_expose] def polynomialToCompletionHom (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α) :
    (polynomialExtension α hα).Hom (completionPresentation I α hα).toExtension where
  toRingHom := (polynomialToCompletionAlgHom I).toRingHom
  toRingHom_algebraMap := polynomialToCompletionHom_toRingHom_algebraMap I α hα
  algebraMap_toRingHom := polynomialToCompletionHom_algebraMap_toRingHom I α hα

end Algebra.NaiveCotangent.Adic
