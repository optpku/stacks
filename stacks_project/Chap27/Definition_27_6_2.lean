module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Graded

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

/- Complete migration checks for the graded-algebra, cone, and vector-bundle API used by
the source-facing specification. -/
#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.GradedQcAlgebra.IsSymmetricPowerComparison :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (A : AlgebraicGeometry.Scheme.GradedQcAlgebra S)
      (comparison : ∀ n : ℕ,
        AlgebraicGeometry.RingedSpace.SymmetricPower.sheaf
            (A.degreePiece 1) n ⟶ A.degreePiece n),
      Prop)

#check
  (AlgebraicGeometry.Scheme.ConeOver :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.ConeHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X X' : AlgebraicGeometry.Scheme.ConeOver S), Type u)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.vectorBundleHomCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (hom : E.V ⟶ E'.V) (overBase : hom ≫ E'.π = E.π), Prop)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E E' : AlgebraicGeometry.Scheme.VectorBundleOver S), Type u)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.toSchemeHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E'), E.V ⟶ E'.V)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.V :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S), AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.π :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S), E.V ⟶ S)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.pushforwardGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.Scheme.GradedQcAlgebra S)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.pushforwardAlgebraIso :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj
          E.pushforwardGrading.algebra ≅
        Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom))

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.isAffineHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.IsAffineHom E.π)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.chosenAlgebra :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.Scheme.QcAlgebraUnder S)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.degreePieceToUnderlyingMap :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S) (n : ℕ),
      E.pushforwardGrading.degreePiece n ⟶
        AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S E.chosenAlgebra)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.underlyingToDegreePieceMap :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S) (n : ℕ),
      AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S E.chosenAlgebra ⟶
        E.pushforwardGrading.degreePiece n)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.degreeZeroIso :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      E.pushforwardGrading.degreePiece 0 ≅ SheafOfModules.unit S.ringCatSheaf)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.degreeZeroHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      E.pushforwardGrading.degreePiece 0 ⟶ SheafOfModules.unit S.ringCatSheaf)

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.pushforwardAlgebraHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj E.chosenAlgebra ⟶
        Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom))

/- Definition 27.6.2: a vector bundle over `S` is an affine scheme over `S` whose actual
pushforward structure algebra is nonnegatively graded, has degree zero `𝒪_S`, and has
canonical multiplication-induced isomorphisms `Sym^n(𝒜₁) ⟶ 𝒜_n` in every degree. -/
@[stacks 062M] #check
  (AlgebraicGeometry.Scheme.VectorBundleOver.ofCone :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (cone : AlgebraicGeometry.Scheme.ConeOver S)
      (symmetricPowerToDegree :
        ∀ n : ℕ, AlgebraicGeometry.RingedSpace.SymmetricPower.sheaf
          (cone.pushforwardGrading.degreePiece 1) n ⟶
            cone.pushforwardGrading.degreePiece n)
      (symmetricPowerToDegree_isCanonical :
        AlgebraicGeometry.Scheme.GradedQcAlgebra.IsSymmetricPowerComparison
          cone.pushforwardGrading symmetricPowerToDegree)
      (symmetricPowerToDegree_isIso :
        ∀ n : ℕ, IsIso (symmetricPowerToDegree n)),
      AlgebraicGeometry.Scheme.VectorBundleOver S)

/- The expanded specification exposes the affine projection, graded pushforward algebra,
degree-zero identification, and symmetric-power isomorphisms of a vector bundle. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.IsAffineHom E.π ∧
        (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V),
          ((E.pushforwardGrading.degreePiece 0).val.map f).hom
              (E.pushforwardGrading.one U) = E.pushforwardGrading.one V) ∧
        (∀ {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
          (a : (E.pushforwardGrading.degreePiece n).val.obj U)
          (b : (E.pushforwardGrading.degreePiece m).val.obj U),
          ((E.pushforwardGrading.degreePiece (n + m)).val.map f).hom
              (E.pushforwardGrading.mul U n m a b) =
            E.pushforwardGrading.mul V n m
              (((E.pushforwardGrading.degreePiece n).val.map f).hom a)
              (((E.pushforwardGrading.degreePiece m).val.map f).hom b)) ∧
        (∀ (U : (Opens S)ᵒᵖ) (i j k : ℕ)
          (a : (E.pushforwardGrading.degreePiece i).val.obj U)
          (b : (E.pushforwardGrading.degreePiece j).val.obj U)
          (c : (E.pushforwardGrading.degreePiece k).val.obj U),
          HEq
            (E.pushforwardGrading.mul U (i + j) k
              (E.pushforwardGrading.mul U i j a b) c)
            (E.pushforwardGrading.mul U i (j + k) a
              (E.pushforwardGrading.mul U j k b c))) ∧
        (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
          (a : (E.pushforwardGrading.degreePiece n).val.obj U),
          HEq (E.pushforwardGrading.mul U 0 n (E.pushforwardGrading.one U) a) a) ∧
        (∀ (U : (Opens S)ᵒᵖ) (n : ℕ)
          (a : (E.pushforwardGrading.degreePiece n).val.obj U),
          HEq (E.pushforwardGrading.mul U n 0 a (E.pushforwardGrading.one U)) a) ∧
        (∃ degreeZeroIso : E.pushforwardGrading.degreePiece 0 ≅
            SheafOfModules.unit S.ringCatSheaf,
          degreeZeroIso = E.pushforwardGrading.degreeZeroIso) ∧
        (∀ n : ℕ,
          E.pushforwardGrading.degreePieceToUnderlying n ≫
              E.pushforwardGrading.underlyingToDegreePiece n =
            𝟙 (E.pushforwardGrading.degreePiece n)) ∧
        (∀ {n m : ℕ}, n ≠ m →
          E.pushforwardGrading.degreePieceToUnderlying n ≫
            E.pushforwardGrading.underlyingToDegreePiece m = 0) ∧
        (∀ (U : (Opens S)ᵒᵖ)
          (a : (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S
            E.pushforwardGrading.algebra).val.obj U),
          ∃ s : Finset ℕ,
            a = Finset.sum s fun n ↦
              (((E.pushforwardGrading.degreePieceToUnderlying n).val.app U).hom)
                ((((E.pushforwardGrading.underlyingToDegreePiece n).val.app U).hom) a)) ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp
          S E.pushforwardGrading ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp
          S E.pushforwardGrading ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.IsSymmetricPowerComparison
          E.pushforwardGrading E.symmetricPowerToDegree ∧
        (∀ n : ℕ, IsIso (E.symmetricPowerToDegree n)) ∧
        (∃ pushforwardAlgebraIso :
            (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj
                E.pushforwardGrading.algebra ≅
              Under.mk
                (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom),
          pushforwardAlgebraIso = E.pushforwardAlgebraIso))

/- A morphism of vector bundles over `S` lies over `S`, and the induced contravariant pullback
on the actual pushforward algebras preserves their chosen gradings. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E'),
      (f.hom ≫ E'.π = E.π) ∧
        AlgebraicGeometry.Scheme.vectorBundleHomCompatibleWithGrading
          S f.hom f.overBase)
