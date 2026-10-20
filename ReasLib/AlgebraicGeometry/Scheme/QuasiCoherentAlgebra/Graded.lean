module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying

/-!
# Explicit gradings of quasi-coherent algebras

This file bundles a nonnegative grading of a chosen quasi-coherent algebra on a scheme.  The
grading is explicit data: no coercions, instances, or inferred category structures are added.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- An explicit nonnegative grading of a chosen quasi-coherent `𝒪_S`-algebra. -/
structure GradedQcAlgebra where
  /-- The chosen quasi-coherent `𝒪_S`-algebra carrying the grading. -/
  algebra : S.QcAlgebraUnder
  /-- The homogeneous degree pieces. -/
  degreePiece : ℕ → S.Modules
  /-- The degree-zero unit section. -/
  one : ∀ U : (Opens S)ᵒᵖ, (degreePiece 0).val.obj U
  /-- Multiplication of homogeneous local sections. -/
  mul :
    ∀ (U : (Opens S)ᵒᵖ) (n m : ℕ),
      (degreePiece n).val.obj U →ₗ[S.presheaf.obj U]
        (degreePiece m).val.obj U →ₗ[S.presheaf.obj U]
          (degreePiece (n + m)).val.obj U
  /-- The homogeneous unit commutes with restriction. -/
  map_one :
    ∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V),
      ((degreePiece 0).val.map f).hom (one U) = one V
  /-- Homogeneous multiplication commutes with restriction. -/
  map_mul :
    ∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
      (a : (degreePiece n).val.obj U) (b : (degreePiece m).val.obj U),
      ((degreePiece (n + m)).val.map f).hom (mul U n m a b) =
        mul V n m (((degreePiece n).val.map f).hom a)
          (((degreePiece m).val.map f).hom b)
  /-- Homogeneous multiplication is associative. -/
  mul_assoc :
    ∀ (U : (Opens S)ᵒᵖ) (i j k : ℕ)
      (a : (degreePiece i).val.obj U) (b : (degreePiece j).val.obj U)
      (c : (degreePiece k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c)
        (mul U i (j + k) a (mul U j k b c))
  /-- The degree-zero unit is a left identity. -/
  one_mul :
    ∀ (U : (Opens S)ᵒᵖ) (n : ℕ) (a : (degreePiece n).val.obj U),
      HEq (mul U 0 n (one U) a) a
  /-- The degree-zero unit is a right identity. -/
  mul_one :
    ∀ (U : (Opens S)ᵒᵖ) (n : ℕ) (a : (degreePiece n).val.obj U),
      HEq (mul U n 0 a (one U)) a
  /-- The inclusion of each degree piece into the underlying algebra module. -/
  degreePieceToUnderlying :
    ∀ n : ℕ, degreePiece n ⟶ QcAlgebraUnder.underlyingModule S algebra
  /-- The projection from the underlying algebra module to each degree piece. -/
  underlyingToDegreePiece :
    ∀ n : ℕ, QcAlgebraUnder.underlyingModule S algebra ⟶ degreePiece n
  /-- The degree-zero piece is identified with `𝒪_S`. -/
  degreeZeroIso : degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf
  /-- Projection to a degree piece splits its inclusion. -/
  degreePiece_split :
    ∀ n : ℕ, degreePieceToUnderlying n ≫ underlyingToDegreePiece n = 𝟙 (degreePiece n)
  /-- Projection to one degree kills inclusions from every other degree. -/
  degreePiece_orthogonal :
    ∀ {n m : ℕ}, n ≠ m → degreePieceToUnderlying n ≫ underlyingToDegreePiece m = 0
  /-- Every local section of the chosen algebra is a finite sum of homogeneous components. -/
  underlying_eq_sum_components :
    ∀ (U : (Opens S)ᵒᵖ)
      (a : (QcAlgebraUnder.underlyingModule S algebra).val.obj U),
      ∃ s : Finset ℕ,
        a = Finset.sum s fun n ↦
          (((degreePieceToUnderlying n).val.app U).hom)
            ((((underlyingToDegreePiece n).val.app U).hom) a)
  /-- Multiplication on the total algebra agrees with homogeneous multiplication. -/
  algebra_respects_grading :
    ∀ (U : (Opens S)ᵒᵖ) (n m : ℕ)
      (a : (degreePiece n).val.obj U) (b : (degreePiece m).val.obj U),
      ((((degreePieceToUnderlying (n + m)).val.app U).hom) (mul U n m a b) :
          (QcAlgebraUnder.sheaf S algebra).1.obj U) =
        (fun (x y : (QcAlgebraUnder.sheaf S algebra).1.obj U) ↦ x * y)
          (((degreePieceToUnderlying n).val.app U).hom a)
          (((degreePieceToUnderlying m).val.app U).hom b)
  /-- The degree-zero identification sends the homogeneous unit to `1`. -/
  degree_zero_unit_compatible :
    ∀ U : (Opens S)ᵒᵖ,
      ((((degreeZeroIso.hom).val.app U).hom) (one U) : S.presheaf.obj U) =
        (1 : S.presheaf.obj U)

namespace GradedQcAlgebra

/-- The proposition that total-algebra multiplication agrees with homogeneous multiplication. -/
def algebraRespectsGradingProp (A : GradedQcAlgebra S) : Prop :=
  ∀ (U : (Opens S)ᵒᵖ) (n m : ℕ)
    (a : (A.degreePiece n).val.obj U) (b : (A.degreePiece m).val.obj U),
    ((((A.degreePieceToUnderlying (n + m)).val.app U).hom) (A.mul U n m a b) :
        (QcAlgebraUnder.sheaf S A.algebra).1.obj U) =
      (fun (x y : (QcAlgebraUnder.sheaf S A.algebra).1.obj U) ↦ x * y)
        (((A.degreePieceToUnderlying n).val.app U).hom a)
        (((A.degreePieceToUnderlying m).val.app U).hom b)

/-- The proposition that the chosen degree-zero identification preserves the unit. -/
def degreeZeroUnitCompatibleProp (A : GradedQcAlgebra S) : Prop :=
  ∀ U : (Opens S)ᵒᵖ,
    ((((A.degreeZeroIso.hom).val.app U).hom) (A.one U) : S.presheaf.obj U) =
      (1 : S.presheaf.obj U)

/-- The canonical degree-`n` component of a quasi-coherent-algebra morphism. -/
def degreeMap {A B : GradedQcAlgebra S} (f : A.algebra ⟶ B.algebra) (n : ℕ) :
    A.degreePiece n ⟶ B.degreePiece n :=
  A.degreePieceToUnderlying n ≫ QcAlgebraUnder.underlyingModuleMap S f ≫
    B.underlyingToDegreePiece n

/-- A concrete quasi-coherent-algebra morphism preserves the two explicit gradings. -/
def IsGradedHom {A B : GradedQcAlgebra S} (f : A.algebra ⟶ B.algebra) : Prop :=
  (∀ U : (Opens S)ᵒᵖ,
      ((((degreeMap S f 0).val.app U).hom) (A.one U)) = B.one U) ∧
    (∀ (U : (Opens S)ᵒᵖ) (n m : ℕ)
      (a : (A.degreePiece n).val.obj U) (b : (A.degreePiece m).val.obj U),
      (((degreeMap S f (n + m)).val.app U).hom) (A.mul U n m a b) =
        B.mul U n m ((((degreeMap S f n).val.app U).hom) a)
          ((((degreeMap S f m).val.app U).hom) b)) ∧
    (∀ n : ℕ,
      degreeMap S f n ≫ B.degreePieceToUnderlying n =
        A.degreePieceToUnderlying n ≫ QcAlgebraUnder.underlyingModuleMap S f) ∧
    (∀ n : ℕ,
      QcAlgebraUnder.underlyingModuleMap S f ≫ B.underlyingToDegreePiece n =
        A.underlyingToDegreePiece n ≫ degreeMap S f n) ∧
    (degreeMap S f 0 ≫ B.degreeZeroIso.hom = A.degreeZeroIso.hom)

/-- The complete specification of an explicit nonnegative grading of a quasi-coherent algebra. -/
theorem spec (A : GradedQcAlgebra S) :
    (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V),
      ((A.degreePiece 0).val.map f).hom (A.one U) = A.one V) ∧
      (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
        (a : (A.degreePiece n).val.obj U) (b : (A.degreePiece m).val.obj U),
        ((A.degreePiece (n + m)).val.map f).hom (A.mul U n m a b) =
          A.mul V n m (((A.degreePiece n).val.map f).hom a)
            (((A.degreePiece m).val.map f).hom b)) ∧
      (∀ (U : (Opens S)ᵒᵖ) (i j k : ℕ)
        (a : (A.degreePiece i).val.obj U) (b : (A.degreePiece j).val.obj U)
        (c : (A.degreePiece k).val.obj U),
        HEq (A.mul U (i + j) k (A.mul U i j a b) c)
          (A.mul U i (j + k) a (A.mul U j k b c))) ∧
      (∀ (U : (Opens S)ᵒᵖ) (n : ℕ) (a : (A.degreePiece n).val.obj U),
        HEq (A.mul U 0 n (A.one U) a) a) ∧
      (∀ (U : (Opens S)ᵒᵖ) (n : ℕ) (a : (A.degreePiece n).val.obj U),
        HEq (A.mul U n 0 a (A.one U)) a) ∧
      (∃ degreeZeroIso : A.degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf,
        degreeZeroIso = A.degreeZeroIso) ∧
      (∀ n : ℕ,
        A.degreePieceToUnderlying n ≫ A.underlyingToDegreePiece n =
          𝟙 (A.degreePiece n)) ∧
      (∀ {n m : ℕ}, n ≠ m →
        A.degreePieceToUnderlying n ≫ A.underlyingToDegreePiece m = 0) ∧
      (∀ (U : (Opens S)ᵒᵖ)
        (a : (QcAlgebraUnder.underlyingModule S A.algebra).val.obj U),
        ∃ s : Finset ℕ,
          a = Finset.sum s fun n ↦
            (((A.degreePieceToUnderlying n).val.app U).hom)
              ((((A.underlyingToDegreePiece n).val.app U).hom) a)) ∧
      algebraRespectsGradingProp S A ∧ degreeZeroUnitCompatibleProp S A := sorry

namespace IsGradedHom

/-- The identity algebra morphism preserves an explicit grading. -/
theorem id (A : GradedQcAlgebra S) : IsGradedHom S (𝟙 A.algebra) := sorry

/-- A composite of grading-preserving algebra morphisms preserves the grading. -/
theorem comp {A B C : GradedQcAlgebra S} {f : A.algebra ⟶ B.algebra}
    {g : B.algebra ⟶ C.algebra} (hf : IsGradedHom S f) (hg : IsGradedHom S g) :
    IsGradedHom S (f ≫ g) := sorry

end IsGradedHom

end GradedQcAlgebra

end AlgebraicGeometry.Scheme
