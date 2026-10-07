module

public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry

/- Complete migration checks for the vector-bundle category and quasicoherent-module API. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleOver :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.VectorBundleOver.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.IsAffineHom E.π ∧
        (∀ {U V : (TopologicalSpace.Opens S)ᵒᵖ} (f : U ⟶ V),
          ((E.pushforwardGrading.degreePiece 0).val.map f).hom
              (E.pushforwardGrading.one U) = E.pushforwardGrading.one V) ∧
        (∀ {U V : (TopologicalSpace.Opens S)ᵒᵖ} (f : U ⟶ V) (n m : ℕ)
          (a : (E.pushforwardGrading.degreePiece n).val.obj U)
          (b : (E.pushforwardGrading.degreePiece m).val.obj U),
          ((E.pushforwardGrading.degreePiece (n + m)).val.map f).hom
              (E.pushforwardGrading.mul U n m a b) =
            E.pushforwardGrading.mul V n m
              (((E.pushforwardGrading.degreePiece n).val.map f).hom a)
              (((E.pushforwardGrading.degreePiece m).val.map f).hom b)) ∧
        (∀ (U : (TopologicalSpace.Opens S)ᵒᵖ) (i j k : ℕ)
          (a : (E.pushforwardGrading.degreePiece i).val.obj U)
          (b : (E.pushforwardGrading.degreePiece j).val.obj U)
          (c : (E.pushforwardGrading.degreePiece k).val.obj U),
          HEq
            (E.pushforwardGrading.mul U (i + j) k
              (E.pushforwardGrading.mul U i j a b) c)
            (E.pushforwardGrading.mul U i (j + k) a
              (E.pushforwardGrading.mul U j k b c))) ∧
        (∀ (U : (TopologicalSpace.Opens S)ᵒᵖ) (n : ℕ)
          (a : (E.pushforwardGrading.degreePiece n).val.obj U),
          HEq (E.pushforwardGrading.mul U 0 n (E.pushforwardGrading.one U) a) a) ∧
        (∀ (U : (TopologicalSpace.Opens S)ᵒᵖ) (n : ℕ)
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
        (∀ (U : (TopologicalSpace.Opens S)ᵒᵖ)
          (a : (AlgebraicGeometry.Scheme.QcAlgebraUnder.underlyingModule S
            E.pushforwardGrading.algebra).val.obj U),
          ∃ s : Finset ℕ,
            a = Finset.sum s fun n ↦
              (((E.pushforwardGrading.degreePieceToUnderlying n).val.app U).hom)
                ((((E.pushforwardGrading.underlyingToDegreePiece n).val.app U).hom) a)) ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.algebraRespectsGradingProp S
          E.pushforwardGrading ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.degreeZeroUnitCompatibleProp S
          E.pushforwardGrading ∧
        AlgebraicGeometry.Scheme.GradedQcAlgebra.IsSymmetricPowerComparison
          E.pushforwardGrading E.symmetricPowerToDegree ∧
        (∀ n : ℕ, IsIso (E.symmetricPowerToDegree n)) ∧
        (∃ pushforwardAlgebraIso :
            (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj
                E.pushforwardGrading.algebra ≅
              Under.mk
                (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap E.π.toShHom),
          pushforwardAlgebraIso = E.pushforwardAlgebraIso))

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E E' : AlgebraicGeometry.Scheme.VectorBundleOver S), Type u)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.spec :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E'),
      (f.hom ≫ E'.π = E.π) ∧
        AlgebraicGeometry.Scheme.vectorBundleHomCompatibleWithGrading S
          f.hom f.overBase)

#check
  (AlgebraicGeometry.Scheme.vectorBundleHomCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (hom : E.V ⟶ E'.V) (overBase : hom ≫ E'.π = E.π), Prop)

#check
  (AlgebraicGeometry.Scheme.QCoh :
    ∀ S : AlgebraicGeometry.Scheme.{u}, Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.QCoh.isWeakSerreClass :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.ObjectProperty.IsWeakSerreClass
        (AlgebraicGeometry.Scheme.quasiCoherentModuleProperty X))

#check
  (AlgebraicGeometry.Scheme.QCoh.closedUnderColimitsOfShape :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) {J : Type v} [CategoryTheory.Category.{w} J],
      CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape
        (AlgebraicGeometry.Scheme.quasiCoherentModuleProperty X) J)

#check
  (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
      (CategoryTheory.Limits.kernel f).IsQuasicoherent)

#check
  (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
      (CategoryTheory.Limits.cokernel f).IsQuasicoherent)

#check
  (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_colimit :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {J : Type v} [CategoryTheory.Category.{w} J]
      (F : J ⥤ X.Modules) [CategoryTheory.Limits.HasColimit F]
      (hF : ∀ j, (F.obj j).IsQuasicoherent),
      (CategoryTheory.Limits.colimit F).IsQuasicoherent)

#check
  (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coproduct :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {ι : Type v} (F : ι → X.Modules)
      [CategoryTheory.Limits.HasCoproduct F]
      (hF : ∀ i, (F i).IsQuasicoherent),
      (∐ F).IsQuasicoherent)

#check
  (AlgebraicGeometry.Scheme.ConeHom.idOverBase :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      (𝟙 X.C) ≫ X.π = X.π)

#check
  (AlgebraicGeometry.Scheme.ConeOver.chosenAlgebraPullback_id :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      AlgebraicGeometry.Scheme.ConeOver.chosenAlgebraPullback S (𝟙 X.C)
          (AlgebraicGeometry.Scheme.ConeHom.idOverBase S X) =
        𝟙 X.pushforwardGrading.algebra)

#check
  (AlgebraicGeometry.Scheme.ConeHom.idCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      AlgebraicGeometry.Scheme.coneHomCompatibleWithGrading S (𝟙 X.C)
        (AlgebraicGeometry.Scheme.ConeHom.idOverBase S X))

#check
  (AlgebraicGeometry.Scheme.ConeHom.id :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (X : AlgebraicGeometry.Scheme.ConeOver S),
      AlgebraicGeometry.Scheme.ConeHom S X X)

#check
  (AlgebraicGeometry.Scheme.ConeHom.compOverBase :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y Z : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X Y)
      (g : AlgebraicGeometry.Scheme.ConeHom S Y Z),
      (f.hom ≫ g.hom) ≫ Z.π = X.π)

#check
  (AlgebraicGeometry.Scheme.ConeOver.chosenAlgebraPullback_comp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y Z : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X Y)
      (g : AlgebraicGeometry.Scheme.ConeHom S Y Z),
      AlgebraicGeometry.Scheme.ConeOver.chosenAlgebraPullback S (f.hom ≫ g.hom)
          (AlgebraicGeometry.Scheme.ConeHom.compOverBase S f g) =
        AlgebraicGeometry.Scheme.ConeOver.chosenAlgebraPullback S g.hom g.overBase ≫
          AlgebraicGeometry.Scheme.ConeOver.chosenAlgebraPullback S f.hom f.overBase)

#check
  (AlgebraicGeometry.Scheme.ConeHom.compCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y Z : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X Y)
      (g : AlgebraicGeometry.Scheme.ConeHom S Y Z),
      AlgebraicGeometry.Scheme.coneHomCompatibleWithGrading S (f.hom ≫ g.hom)
        (AlgebraicGeometry.Scheme.ConeHom.compOverBase S f g))

#check
  (AlgebraicGeometry.Scheme.ConeHom.comp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y Z : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X Y)
      (g : AlgebraicGeometry.Scheme.ConeHom S Y Z),
      AlgebraicGeometry.Scheme.ConeHom S X Z)

#check
  (AlgebraicGeometry.Scheme.ConeHom.ext :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y : AlgebraicGeometry.Scheme.ConeOver S}
      {f g : AlgebraicGeometry.Scheme.ConeHom S X Y},
      f.hom = g.hom → f = g)

#check
  (AlgebraicGeometry.Scheme.ConeHom.id_comp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X Y),
      AlgebraicGeometry.Scheme.ConeHom.comp S
          (AlgebraicGeometry.Scheme.ConeHom.id S X) f = f)

#check
  (AlgebraicGeometry.Scheme.ConeHom.comp_id :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {X Y : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S X Y),
      AlgebraicGeometry.Scheme.ConeHom.comp S f
          (AlgebraicGeometry.Scheme.ConeHom.id S Y) = f)

#check
  (AlgebraicGeometry.Scheme.ConeHom.assoc :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {W X Y Z : AlgebraicGeometry.Scheme.ConeOver S}
      (f : AlgebraicGeometry.Scheme.ConeHom S W X)
      (g : AlgebraicGeometry.Scheme.ConeHom S X Y)
      (h : AlgebraicGeometry.Scheme.ConeHom S Y Z),
      AlgebraicGeometry.Scheme.ConeHom.comp S
          (AlgebraicGeometry.Scheme.ConeHom.comp S f g) h =
        AlgebraicGeometry.Scheme.ConeHom.comp S f
          (AlgebraicGeometry.Scheme.ConeHom.comp S g h))

#check
  (AlgebraicGeometry.Scheme.coneCategory :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.Category (AlgebraicGeometry.Scheme.ConeOver S))

#check
  (AlgebraicGeometry.Scheme.coneCat :
    ∀ S : AlgebraicGeometry.Scheme.{u}, CategoryTheory.Cat.{u, u + 1})

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.idOverBase :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      (𝟙 E.V) ≫ E.π = E.π)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.idCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.Scheme.vectorBundleHomCompatibleWithGrading S (𝟙 E.V)
        (AlgebraicGeometry.Scheme.VectorBundleHom.idOverBase S E))

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.id :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (E : AlgebraicGeometry.Scheme.VectorBundleOver S),
      AlgebraicGeometry.Scheme.VectorBundleHom S E E)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.compOverBase :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' E'' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E')
      (g : AlgebraicGeometry.Scheme.VectorBundleHom S E' E''),
      (f.hom ≫ g.hom) ≫ E''.π = E.π)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.compCompatibleWithGrading :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' E'' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E')
      (g : AlgebraicGeometry.Scheme.VectorBundleHom S E' E''),
      AlgebraicGeometry.Scheme.vectorBundleHomCompatibleWithGrading S (f.hom ≫ g.hom)
        (AlgebraicGeometry.Scheme.VectorBundleHom.compOverBase S f g))

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.comp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' E'' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E')
      (g : AlgebraicGeometry.Scheme.VectorBundleHom S E' E''),
      AlgebraicGeometry.Scheme.VectorBundleHom S E E'')

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.id_comp :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E'),
      AlgebraicGeometry.Scheme.VectorBundleHom.comp S
          (AlgebraicGeometry.Scheme.VectorBundleHom.id S E) f = f)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.comp_id :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E'),
      AlgebraicGeometry.Scheme.VectorBundleHom.comp S f
          (AlgebraicGeometry.Scheme.VectorBundleHom.id S E') = f)

#check
  (AlgebraicGeometry.Scheme.VectorBundleHom.assoc :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      {E E' E'' E''' : AlgebraicGeometry.Scheme.VectorBundleOver S}
      (f : AlgebraicGeometry.Scheme.VectorBundleHom S E E')
      (g : AlgebraicGeometry.Scheme.VectorBundleHom S E' E'')
      (h : AlgebraicGeometry.Scheme.VectorBundleHom S E'' E'''),
      AlgebraicGeometry.Scheme.VectorBundleHom.comp S
          (AlgebraicGeometry.Scheme.VectorBundleHom.comp S f g) h =
        AlgebraicGeometry.Scheme.VectorBundleHom.comp S f
          (AlgebraicGeometry.Scheme.VectorBundleHom.comp S g h))

#check
  (AlgebraicGeometry.Scheme.vectorBundleCategory :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.Category (AlgebraicGeometry.Scheme.VectorBundleOver S))

#check
  (AlgebraicGeometry.Scheme.vectorBundleCat :
    ∀ S : AlgebraicGeometry.Scheme.{u}, CategoryTheory.Cat.{u, u + 1})

#check
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

/- Lemma 27.6.3: the category of vector bundles over `S` is anti-equivalent to the category
of quasicoherent `𝒪_S`-modules. -/
@[stacks 062N] #check
  (AlgebraicGeometry.Scheme.vectorBundleOverOpEquivQCoh :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      Nonempty ((AlgebraicGeometry.Scheme.vectorBundleCat S)ᵒᵖ ≌
        AlgebraicGeometry.Scheme.QCoh S))

end AlgebraicGeometry
