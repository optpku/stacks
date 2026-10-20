module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import stacks_project.Chap67.Definition_67_13_2_InverseImage

/-!
# Inverse images of open subspaces of algebraic spaces

The inverse image of an open subspace `U` of an algebraic space `X` along a
morphism `φ : Y ⟶ X` is the fibre product `U ×_X Y`, viewed as an open
subspace of `Y`. The fibre product is formed in the functor-of-points
category, parallel to the closed inverse image.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImage :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι],
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImage_functorOfPoints :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    (openInverseImage φ ι).functorOfPoints =
      pullback (toFunctorOfPoints φ) (toFunctorOfPoints ι))

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImageι :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι],
    openInverseImage φ ι ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImageTo :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S} (φ : Y ⟶ X)
    (ι : U ⟶ X) [IsOpenImmersion ι],
    openInverseImage φ ι ⟶ U)

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImageι_eq_fst :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    toFunctorOfPoints (openInverseImageι φ ι) =
      pullback.fst (toFunctorOfPoints φ) (toFunctorOfPoints ι))

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImageTo_eq_snd :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    toFunctorOfPoints (openInverseImageTo φ ι) =
      pullback.snd (toFunctorOfPoints φ) (toFunctorOfPoints ι))

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImage_condition :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    openInverseImageι φ ι ≫ φ = openInverseImageTo φ ι ≫ ι)

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImage_isPullback :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    IsPullback (openInverseImageι φ ι) (openInverseImageTo φ ι) φ ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y U P : AlgebraicSpace S}
    {f : Y ⟶ X} {ι : U ⟶ X} {pY : P ⟶ Y} {pU : P ⟶ U} [IsOpenImmersion ι]
    (h : IsPullback pY pU f ι),
    IsOpenImmersion pY)

#check (AlgebraicGeometry.AlgebraicSpace.instIsOpenImmersion_openInverseImageι :
  ∀ {S : Scheme.{u}}
    {X Y U : AlgebraicSpace S} (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    IsOpenImmersion (openInverseImageι φ ι))

#check (AlgebraicGeometry.AlgebraicSpace.openInverseImage_spec :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (φ : Y ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι],
    (openInverseImage φ ι).functorOfPoints =
        pullback (toFunctorOfPoints φ) (toFunctorOfPoints ι) ∧
      toFunctorOfPoints (openInverseImageι φ ι) =
        pullback.fst (toFunctorOfPoints φ) (toFunctorOfPoints ι) ∧
      IsOpenImmersion (openInverseImageι φ ι) ∧
      IsPullback (openInverseImageι φ ι) (openInverseImageTo φ ι) φ ι)

end AlgebraicGeometry.AlgebraicSpace
