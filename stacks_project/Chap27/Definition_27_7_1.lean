/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cone.Construction
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory
open TopologicalSpace

/- Definition 27.7.1: let `S` be a scheme and let `𝒜` be a quasi-coherent graded
`𝒪_S`-algebra such that `𝒪_S ≅ 𝒜 0`. Its associated cone, or affine cone, is
`C(𝒜) = underlineSpec_S(𝒜)`, the relative spectrum of its underlying quasi-coherent
`𝒪_S`-algebra. Here `P` is an explicit chosen relative-spectrum model. -/
@[stacks 062Q] #check (AlgebraicGeometry.Scheme.affineCone_eq_relativeSpec :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A.algebra)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.affineCone A P =
        AlgebraicGeometry.Scheme.relativeSpec P)

/- The affine-cone construction from a valid chosen relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.affineCone :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A.algebra)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.{u})

/- The explicit grading data includes the degree-zero identification and unit compatibility. -/
#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra :
    AlgebraicGeometry.Scheme.{u} → Type (u + 1))

/- The proposition that total-algebra multiplication agrees with homogeneous multiplication. -/
#check (AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S), Prop)

/- The proposition that the chosen degree-zero identification preserves the unit. -/
#check (AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S), Prop)

/- The canonical degree component of a quasi-coherent-algebra morphism. -/
#check (AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeMap :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {A B : AlgebraicGeometry.Scheme.GradedQcAlgebra S}
      (f : A.algebra ⟶ B.algebra) (n : ℕ),
      A.degreePiece n ⟶ B.degreePiece n)

/- The proposition that a fixed algebra morphism preserves two explicit gradings. -/
#check (AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {A B : AlgebraicGeometry.Scheme.GradedQcAlgebra S}
      (f : A.algebra ⟶ B.algebra), Prop)

/- The explicit data owner for a chosen relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.RelativeSpectrumOver :
    {S : AlgebraicGeometry.Scheme.{u}} → S.QcAlgebraUnder → Type (u + 1))

/- The universal relative-spectrum point carried by a chosen model. -/
#check (AlgebraicGeometry.Scheme.RelativeSpectrumOver.point :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      AlgebraicGeometry.Scheme.relativeSpectrumPair A P.scheme)

/- The validity predicate for a fixed chosen relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.IsRelativeSpectrumOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder},
      AlgebraicGeometry.Scheme.RelativeSpectrumOver A → Prop)

/- The scheme underlying a chosen relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpec :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (_P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      AlgebraicGeometry.Scheme.{u})

/- The universal point of a chosen relative-spectrum model. -/
#check (AlgebraicGeometry.Scheme.relativeSpecPoint :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      AlgebraicGeometry.Scheme.relativeSpectrumPair A
        (AlgebraicGeometry.Scheme.relativeSpec P))

/- The structural morphism of a chosen relative-spectrum model. -/
#check (AlgebraicGeometry.Scheme.relativeSpecπ :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      P.scheme ⟶ S)

/- The complete laws satisfied by an explicit nonnegative grading. -/
#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S),
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
          (a : (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule
            S A.algebra).val.obj U),
          ∃ s : Finset ℕ,
            a = Finset.sum s fun n ↦
              (((A.degreePieceToUnderlying n).val.app U).hom)
                ((((A.underlyingToDegreePiece n).val.app U).hom) a)) ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp S A ∧
          AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp S A)

/- The identity algebra morphism preserves an explicit grading. -/
#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom.id :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S),
      AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom S (𝟙 A.algebra))

/- Composition preserves grading-compatible algebra morphisms. -/
#check (AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom.comp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {A B C : AlgebraicGeometry.Scheme.GradedQcAlgebra S}
      {f : A.algebra ⟶ B.algebra} {g : B.algebra ⟶ C.algebra}
      (hf : AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom S f)
      (hg : AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom S g),
      AlgebraicGeometry.Scheme.GradedQcAlgebra.IsGradedHom S (f ≫ g))

/- The universal point of a valid chosen model represents the relative-spectrum functor. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecPoint_isRepresentedBy :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy
        (AlgebraicGeometry.Scheme.relativeSpecPoint P))

/- The structural morphism of a valid chosen model realizes the relative spectrum. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecπ_realizesRelativeSpectrum :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum A
        (AlgebraicGeometry.Scheme.relativeSpecπ P))
