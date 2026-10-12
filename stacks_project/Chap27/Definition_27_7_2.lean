/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cone.Category

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open TopologicalSpace

universe u

/- Companion checks for the canonical quasi-coherent and graded-algebra API used below. -/
#check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.sheaf :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (A : S.QcAlgebraUnder),
      CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u})

#check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (A : S.QcAlgebraUnder), S.Modules)

#check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModuleMap :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) {A B : S.QcAlgebraUnder} (f : A ⟶ B),
      AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S A ⟶
        AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S B)

#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S),
      A.degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf)

#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S), Prop)

#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S), Prop)

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
        (a : (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S
          A.algebra).val.obj U),
        ∃ s : Finset ℕ,
          a = Finset.sum s fun n ↦
            (((A.degreePieceToUnderlying n).val.app U).hom)
              ((((A.underlyingToDegreePiece n).val.app U).hom) a)) ∧
      AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp S A ∧
      AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp S A)

#check
  (AlgebraicGeometry.Scheme.ConeOver :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.ConeOver.isAffineHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      AlgebraicGeometry.IsAffineHom X.π)

#check
  (AlgebraicGeometry.Scheme.ConeOver.degreeZeroIso :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      X.pushforwardGrading.degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf)

#check
  (AlgebraicGeometry.Scheme.inducedConePushforwardPullback :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X X' : AlgebraicGeometry.Scheme.ConeOver S}
      (hom : X.C ⟶ X'.C) (overBase : hom ≫ X'.π = X.π),
      Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap X'.π.toShHom) ⟶
        Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap X.π.toShHom))

#check
  (AlgebraicGeometry.Scheme.coneHomCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X X' : AlgebraicGeometry.Scheme.ConeOver S}
      (hom : X.C ⟶ X'.C) (overBase : hom ≫ X'.π = X.π), Prop)

#check
  (AlgebraicGeometry.Scheme.ConeHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X X' : AlgebraicGeometry.Scheme.ConeOver S), Type u)

#check
  (AlgebraicGeometry.Scheme.ConeHom.toSchemeHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X X' : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X X'), X.C ⟶ X'.C)

#check
  (AlgebraicGeometry.Scheme.coneCategory :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.Category (AlgebraicGeometry.Scheme.ConeOver S))

/- Definition 27.7.2: a cone over `S` is an affine morphism whose actual pushforward
structure algebra has an explicit `ℕ`-grading, finite homogeneous decomposition, compatible
multiplication, and degree-zero piece identified with `𝒪_S`. -/
@[stacks 062R] #check
  (AlgebraicGeometry.Scheme.ConeOver.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      AlgebraicGeometry.IsAffineHom X.π ∧
        (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V),
          ((X.pushforwardGrading.degreePiece 0).val.map f).hom
              (X.pushforwardGrading.one U) = X.pushforwardGrading.one V) ∧
        (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
          (a : (X.pushforwardGrading.degreePiece n).val.obj U)
          (b : (X.pushforwardGrading.degreePiece m).val.obj U),
          ((X.pushforwardGrading.degreePiece (n + m)).val.map f).hom
              (X.pushforwardGrading.mul U n m a b) =
            X.pushforwardGrading.mul V n m
              (((X.pushforwardGrading.degreePiece n).val.map f).hom a)
              (((X.pushforwardGrading.degreePiece m).val.map f).hom b)) ∧
        (∀ (U : (Opens S)ᵒᵖ) (i j k : ℕ)
          (a : (X.pushforwardGrading.degreePiece i).val.obj U)
          (b : (X.pushforwardGrading.degreePiece j).val.obj U)
          (c : (X.pushforwardGrading.degreePiece k).val.obj U),
          HEq
            (X.pushforwardGrading.mul U (i + j) k
              (X.pushforwardGrading.mul U i j a b) c)
            (X.pushforwardGrading.mul U i (j + k) a
              (X.pushforwardGrading.mul U j k b c))) ∧
        (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
          (a : (X.pushforwardGrading.degreePiece n).val.obj U),
          HEq (X.pushforwardGrading.mul U 0 n (X.pushforwardGrading.one U) a) a) ∧
        (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
          (a : (X.pushforwardGrading.degreePiece n).val.obj U),
          HEq (X.pushforwardGrading.mul U n 0 a (X.pushforwardGrading.one U)) a) ∧
        (∃ degreeZeroIso : X.pushforwardGrading.degreePiece 0 ≅
            SheafOfModules.unit S.ringCatSheaf,
          degreeZeroIso = X.pushforwardGrading.degreeZeroIso) ∧
        (∀ n : ℕ,
          X.pushforwardGrading.degreePieceToUnderlying n ≫
              X.pushforwardGrading.underlyingToDegreePiece n =
            𝟙 (X.pushforwardGrading.degreePiece n)) ∧
        (∀ {n m : ℕ}, n ≠ m →
          X.pushforwardGrading.degreePieceToUnderlying n ≫
            X.pushforwardGrading.underlyingToDegreePiece m = 0) ∧
        (∀ (U : (Opens S)ᵒᵖ)
          (a : (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S
            X.pushforwardGrading.algebra).val.obj U),
          ∃ s : Finset ℕ,
            a = Finset.sum s fun n ↦
              (((X.pushforwardGrading.degreePieceToUnderlying n).val.app U).hom)
                ((((X.pushforwardGrading.underlyingToDegreePiece n).val.app U).hom) a)) ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp S
          X.pushforwardGrading ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp S
          X.pushforwardGrading ∧
        (∃ pushforwardAlgebraIso :
            (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj
                X.pushforwardGrading.algebra ≅
              Under.mk
                (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap X.π.toShHom),
          pushforwardAlgebraIso = X.pushforwardAlgebraIso))

/- Companion check: a morphism of cones lies over the fixed base and its induced
contravariant map on the chosen pushforward algebras preserves the explicit gradings. -/
#check
  (AlgebraicGeometry.Scheme.ConeHom.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X X' : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X X'),
      (f.hom ≫ X'.π = X.π) ∧
        AlgebraicGeometry.Scheme.coneHomCompatibleWithGrading S f.hom f.overBase)
