module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Difference
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Diagonal

/-!
# Diagonal construction of difference conormal maps

Two morphisms over a scheme determine an ordered map to the relative self-product. When they
agree along an immersion, this map compares the relative diagonal conormal sheaf with the
conormal sheaf of the immersion and identifies the resulting map with their difference
derivation.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y : Scheme.{u}}

/-- The two morphisms over `S` defining the ordered pair `(b', a')` have equal composites to
`S`. -/
theorem differencePair_fac (S : Scheme.{u}) {X' Y : Scheme.{u}}
    [X'.Over S] [Y.Over S] (a' b' : X' ⟶ Y) [a'.IsOver S] [b'.IsOver S] :
    b' ≫ (Y ↘ S) = a' ≫ (Y ↘ S) := sorry

/-- The morphism to the relative self-product whose ordered components are `(b', a')`. -/
noncomputable def differencePair (S : Scheme.{u}) {X' Y : Scheme.{u}}
    [X'.Over S] [Y.Over S] (a' b' : X' ⟶ Y) [a'.IsOver S] [b'.IsOver S] :
    X' ⟶ pullback (Y ↘ S) (Y ↘ S) :=
  pullback.lift b' a' (differencePair_fac S a' b')

/-- The first projection of `differencePair` is `b'`. -/
theorem differencePair_fst (S : Scheme.{u}) {X' Y : Scheme.{u}}
    [X'.Over S] [Y.Over S] (a' b' : X' ⟶ Y) [a'.IsOver S] [b'.IsOver S] :
    differencePair S a' b' ≫ pullback.fst (Y ↘ S) (Y ↘ S) = b' := sorry

/-- The second projection of `differencePair` is `a'`. -/
theorem differencePair_snd (S : Scheme.{u}) {X' Y : Scheme.{u}}
    [X'.Over S] [Y.Over S] (a' b' : X' ⟶ Y) [a'.IsOver S] [b'.IsOver S] :
    differencePair S a' b' ≫ pullback.snd (Y ↘ S) (Y ↘ S) = a' := sorry

/-- Common restrictions of two morphisms induce a square from the immersion to the relative
diagonal. -/
theorem differenceSquare (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    (a' b' : X' ⟶ Y) [X'.Over S] [Y.Over S] [a'.IsOver S] [b'.IsOver S]
    (sqA : CommSq a i (𝟙 Y) a') (sqB : CommSq a i (𝟙 Y) b') :
    CommSq a i (pullback.diagonal (Y ↘ S)) (differencePair S a' b') := sorry

/-- The map from the pullback of relative differentials to the conormal sheaf induced by the
relative diagonal square associated to `(b', a')`. -/
noncomputable def differenceConormalMap (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    (a' b' : X' ⟶ Y) [X'.Over S] [Y.Over S] [a'.IsOver S] [b'.IsOver S]
    (sqA : CommSq a i (𝟙 Y) a') (sqB : CommSq a i (𝟙 Y) b') :
    (Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶ conormalSheaf i :=
  (Modules.pullback a).map (RelativeDifferentials.Diagonal.comparison (Y ↘ S)) ≫
    Conormal.map (differenceSquare S i a a' b' sqA sqB)

/-- The difference conormal map is the pullback of the diagonal comparison followed by the
conormal comparison of the induced square. -/
theorem differenceConormalMap_def (S : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    (a' b' : X' ⟶ Y) [X'.Over S] [Y.Over S] [a'.IsOver S] [b'.IsOver S]
    (sqA : CommSq a i (𝟙 Y) a') (sqB : CommSq a i (𝟙 Y) b') :
    differenceConormalMap S i a a' b' sqA sqB =
      (Modules.pullback a).map (RelativeDifferentials.Diagonal.comparison (Y ↘ S)) ≫
        Conormal.map (differenceSquare S i a a' b' sqA sqB) := sorry

/-- A derivation realizing the sectionwise difference between two lifts is the universal
relative derivation postcomposed with the adjoint of their difference conormal map. -/
theorem differenceDerivation_eq_postcomp (i : X ⟶ X') (a : X ⟶ Y)
    (a' b' : X' ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S]
    [IsFirstOrderThickening i] [i.IsOver S] [a.IsOver S] [a'.IsOver S] [b'.IsOver S]
    (sqA : CommSq a i (𝟙 Y) a') (sqB : CommSq a i (𝟙 Y) b')
    (D : RingedSpace.Hom.derivations (Y ↘ S).toShHom
      ((Modules.pushforward a).obj (conormalSheaf i)))
    (hD : ∀ (U : (Opens Y)ᵒᵖ)
      (x : (IsFirstOrderThickening.presentationSheaf (𝟙 Y)).obj.obj U),
      (presentationDifference sqA sqB).hom.app U x =
        (SquareZeroExtension.conormalInclusion
          (IsFirstOrderThickening.presentationProjection i)
          (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
            ((Opens.map a.base).op.obj U)
            (D.d ((IsFirstOrderThickening.presentationProjection (𝟙 Y)).hom.app U x))) :
    D = (d[(Y ↘ S).toShHom]).postcomp
      (((Modules.pullbackPushforwardAdjunction a).homEquiv _ _)
        (differenceConormalMap S i a a' b' sqA sqB)).val := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
