module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import stacks_project.Chap57.Example_57_8_6_Diagonal
public import stacks_project.Chap57.Lemma_57_8_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A smooth proper scheme over a fixed base scheme. -/
structure FourierMukaiObject (S : Scheme.{u}) where
  scheme : Scheme.{u}
  hom : scheme ⟶ S
  smooth : Smooth hom
  proper : IsProper hom

/-- Isomorphism classes of perfect derived kernels on the fibre product of two objects. -/
abbrev fourierMukaiHom {S : Scheme.{u}} (X Y : FourierMukaiObject S) : Type _ :=
  isomorphismClasses.obj (Cat.of
    (@RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace))

/-- Fourier--Mukai morphisms are isomorphism classes of perfect kernels. -/
theorem fourierMukaiHom_eq {S : Scheme.{u}} (X Y : FourierMukaiObject S) :
    fourierMukaiHom X Y =
      isomorphismClasses.obj (Cat.of
        (@RingedSpace.ModuleDerived.Perfect
          (Limits.pullback X.hom Y.hom).toRingedSpace)) := sorry

/-- The relative diagonal kernel of a smooth proper object is perfect. -/
theorem FourierMukaiObject.diagonalKernel_isPerfect
    {S : Scheme.{u}} (X : FourierMukaiObject S) :
    RingedSpace.ModuleDerived.IsPerfect
      (Scheme.FourierMukai.relativeDiagonalKernel X.hom) := sorry

/-- The canonical perfect identity kernel of a Fourier--Mukai object. -/
noncomputable def FourierMukaiObject.diagonalKernel
    {S : Scheme.{u}} (X : FourierMukaiObject S) :
    @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace :=
  ⟨Scheme.FourierMukai.relativeDiagonalKernel X.hom,
    FourierMukaiObject.diagonalKernel_isPerfect X⟩

/-- The underlying object of the identity kernel is the relative diagonal pushforward. -/
theorem FourierMukaiObject.diagonalKernel_obj
    {S : Scheme.{u}} (X : FourierMukaiObject S) :
    (FourierMukaiObject.diagonalKernel X).obj =
      Scheme.FourierMukai.relativeDiagonalKernel X.hom := sorry

/-- The identity morphism represented by the canonical relative diagonal kernel. -/
noncomputable def FourierMukaiObject.diagonalKernelClass
    {S : Scheme.{u}} (X : FourierMukaiObject S) : fourierMukaiHom X X :=
  Quotient.mk'' (FourierMukaiObject.diagonalKernel X)

/-- The canonical triple fibre product used to convolve two relative kernels. -/
noncomputable def FourierMukaiObject.tripleProduct
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) : Scheme.{u} :=
  Limits.pullback
    (Limits.pullback.fst X.hom Y.hom ≫ X.hom) Z.hom

/-- The first projection from the canonical triple product to `X ×_S Y`. -/
noncomputable def FourierMukaiObject.convolutionP12
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.tripleProduct X Y Z ⟶ Limits.pullback X.hom Y.hom :=
  Limits.pullback.fst
    (Limits.pullback.fst X.hom Y.hom ≫ X.hom) Z.hom

/-- The last projection from the canonical triple product to `Z`. -/
noncomputable def FourierMukaiObject.convolutionP3
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.tripleProduct X Y Z ⟶ Z.scheme :=
  Limits.pullback.snd
    (Limits.pullback.fst X.hom Y.hom ≫ X.hom) Z.hom

/-- The defining projections of the canonical triple product commute over `S`. -/
theorem FourierMukaiObject.tripleProduct_condition
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.convolutionP12 X Y Z ≫
        (Limits.pullback.fst X.hom Y.hom ≫ X.hom) =
      FourierMukaiObject.convolutionP3 X Y Z ≫ Z.hom := sorry

/-- The two legs used to define the projection to `Y ×_S Z` are compatible. -/
theorem FourierMukaiObject.convolutionP23_condition
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    (FourierMukaiObject.convolutionP12 X Y Z ≫
      Limits.pullback.snd X.hom Y.hom) ≫ Y.hom =
      FourierMukaiObject.convolutionP3 X Y Z ≫ Z.hom := sorry

/-- The canonical projection from the triple product to `Y ×_S Z`. -/
noncomputable def FourierMukaiObject.convolutionP23
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.tripleProduct X Y Z ⟶ Limits.pullback Y.hom Z.hom :=
  Limits.pullback.lift
    (FourierMukaiObject.convolutionP12 X Y Z ≫
      Limits.pullback.snd X.hom Y.hom)
    (FourierMukaiObject.convolutionP3 X Y Z)
    (FourierMukaiObject.convolutionP23_condition X Y Z)

/-- The first leg of the projection to `Y ×_S Z` is the expected composite. -/
theorem FourierMukaiObject.convolutionP23_fst
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.convolutionP23 X Y Z ≫
        Limits.pullback.fst Y.hom Z.hom =
      FourierMukaiObject.convolutionP12 X Y Z ≫
        Limits.pullback.snd X.hom Y.hom := sorry

/-- The two legs used to define the projection to `X ×_S Z` are compatible. -/
theorem FourierMukaiObject.convolutionP13_condition
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    (FourierMukaiObject.convolutionP12 X Y Z ≫
      Limits.pullback.fst X.hom Y.hom) ≫ X.hom =
      FourierMukaiObject.convolutionP3 X Y Z ≫ Z.hom := sorry

/-- The canonical projection from the triple product to `X ×_S Z`. -/
noncomputable def FourierMukaiObject.convolutionP13
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.tripleProduct X Y Z ⟶ Limits.pullback X.hom Z.hom :=
  Limits.pullback.lift
    (FourierMukaiObject.convolutionP12 X Y Z ≫
      Limits.pullback.fst X.hom Y.hom)
    (FourierMukaiObject.convolutionP3 X Y Z)
    (FourierMukaiObject.convolutionP13_condition X Y Z)

/-- The first leg of the projection to `X ×_S Z` is the expected composite. -/
theorem FourierMukaiObject.convolutionP13_fst
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S) :
    FourierMukaiObject.convolutionP13 X Y Z ≫
        Limits.pullback.fst X.hom Z.hom =
      FourierMukaiObject.convolutionP12 X Y Z ≫
        Limits.pullback.fst X.hom Y.hom := sorry

/-- The explicit derived pullback--tensor--pushforward convolution of two perfect kernels. -/
noncomputable def FourierMukaiObject.convolutionKernelUnderlying
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (L : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback Y.hom Z.hom).toRingedSpace) :
    RingedSpace.ModuleDerived (Limits.pullback X.hom Z.hom).toRingedSpace :=
  Scheme.FourierMukai.convolutionKernel X.hom Y.hom Z.hom
    (FourierMukaiObject.convolutionP12 X Y Z)
    (FourierMukaiObject.convolutionP23 X Y Z)
    (FourierMukaiObject.convolutionP13 X Y Z) K.obj L.obj

/-- The canonical convolution of perfect kernels is perfect. -/
theorem FourierMukaiObject.convolutionKernelUnderlying_isPerfect
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (L : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback Y.hom Z.hom).toRingedSpace) :
    RingedSpace.ModuleDerived.IsPerfect
      (FourierMukaiObject.convolutionKernelUnderlying X Y Z K L) := sorry

/-- The canonical convolution as a perfect derived kernel. -/
noncomputable def FourierMukaiObject.convolutionKernel
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (L : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback Y.hom Z.hom).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Z.hom).toRingedSpace :=
  ⟨FourierMukaiObject.convolutionKernelUnderlying X Y Z K L,
    FourierMukaiObject.convolutionKernelUnderlying_isPerfect X Y Z K L⟩

/-- The underlying object of canonical convolution is the explicit derived convolution kernel. -/
theorem FourierMukaiObject.convolutionKernel_obj
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (L : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback Y.hom Z.hom).toRingedSpace) :
    (FourierMukaiObject.convolutionKernel X Y Z K L).obj =
      FourierMukaiObject.convolutionKernelUnderlying X Y Z K L := sorry

/-- Convolution carries isomorphic pairs of kernels to isomorphic kernels. -/
theorem FourierMukaiObject.convolutionKernel_respects
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S)
    (K K' : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (hK : CategoryTheory.IsIsomorphic K K')
    (L L' : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback Y.hom Z.hom).toRingedSpace)
    (hL : CategoryTheory.IsIsomorphic L L') :
    CategoryTheory.IsIsomorphic
      (FourierMukaiObject.convolutionKernel X Y Z K L)
      (FourierMukaiObject.convolutionKernel X Y Z K' L') := sorry

/-- Composition of Fourier--Mukai morphisms, induced by canonical derived convolution. -/
noncomputable def FourierMukaiObject.derivedConvolution
    {S : Scheme.{u}} {X Y Z : FourierMukaiObject S} :
    fourierMukaiHom X Y → fourierMukaiHom Y Z → fourierMukaiHom X Z :=
  Quotient.map₂ (FourierMukaiObject.convolutionKernel X Y Z)
    (FourierMukaiObject.convolutionKernel_respects X Y Z)

/-- Derived convolution sends represented classes to the class of the explicit convolution. -/
theorem FourierMukaiObject.derivedConvolution_mk
    {S : Scheme.{u}} (X Y Z : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (L : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback Y.hom Z.hom).toRingedSpace) :
    FourierMukaiObject.derivedConvolution (Quotient.mk'' K) (Quotient.mk'' L) =
      Quotient.mk'' (FourierMukaiObject.convolutionKernel X Y Z K L) := sorry

/-- Derived convolution is left-unital for the canonical diagonal kernel. -/
theorem FourierMukaiObject.diagonalKernelClass_comp
    {S : Scheme.{u}} {X Y : FourierMukaiObject S} (K : fourierMukaiHom X Y) :
    FourierMukaiObject.derivedConvolution
      (FourierMukaiObject.diagonalKernelClass X) K = K := sorry

/-- Derived convolution is right-unital for the canonical diagonal kernel. -/
theorem FourierMukaiObject.comp_diagonalKernelClass
    {S : Scheme.{u}} {X Y : FourierMukaiObject S} (K : fourierMukaiHom X Y) :
    FourierMukaiObject.derivedConvolution K
      (FourierMukaiObject.diagonalKernelClass Y) = K := sorry

/-- Canonical derived convolution is associative on kernel isomorphism classes. -/
theorem FourierMukaiObject.derivedConvolution_assoc
    {S : Scheme.{u}} {W X Y Z : FourierMukaiObject S}
    (K : fourierMukaiHom W X) (L : fourierMukaiHom X Y)
    (M : fourierMukaiHom Y Z) :
    FourierMukaiObject.derivedConvolution
      (FourierMukaiObject.derivedConvolution K L) M =
      FourierMukaiObject.derivedConvolution K
        (FourierMukaiObject.derivedConvolution L M) := sorry

/-- The category whose morphisms are perfect-kernel isomorphism classes and whose composition is
canonical derived convolution. -/
noncomputable instance fourierMukaiObjectCategory (S : Scheme.{u}) :
    Category (FourierMukaiObject S) where
  Hom X Y := fourierMukaiHom X Y
  id := FourierMukaiObject.diagonalKernelClass
  comp := FourierMukaiObject.derivedConvolution
  id_comp := FourierMukaiObject.diagonalKernelClass_comp
  comp_id := FourierMukaiObject.comp_diagonalKernelClass
  assoc := FourierMukaiObject.derivedConvolution_assoc

/-- The categorical identity is represented by the canonical relative diagonal kernel. -/
theorem fourierMukaiObject_id {S : Scheme.{u}} (X : FourierMukaiObject S) :
    𝟙 X = FourierMukaiObject.diagonalKernelClass X := sorry

/-- Smoothness of the canonical pullback object. -/
theorem FourierMukaiObject.baseChange_smooth
    {S S' : Scheme.{u}} (g : S' ⟶ S) (X : FourierMukaiObject S) :
    Smooth (Limits.pullback.fst g X.hom) := sorry

/-- Properness of the canonical pullback object. -/
theorem FourierMukaiObject.baseChange_proper
    {S S' : Scheme.{u}} (g : S' ⟶ S) (X : FourierMukaiObject S) :
    IsProper (Limits.pullback.fst g X.hom) := sorry

/-- The canonical base-changed smooth proper scheme. -/
@[reducible]
noncomputable def FourierMukaiObject.baseChange
    {S S' : Scheme.{u}} (g : S' ⟶ S) (X : FourierMukaiObject S) :
    FourierMukaiObject S' where
  scheme := Limits.pullback g X.hom
  hom := Limits.pullback.fst g X.hom
  smooth := FourierMukaiObject.baseChange_smooth g X
  proper := FourierMukaiObject.baseChange_proper g X

/-- The projection from the base-changed object to the original object. -/
noncomputable def FourierMukaiObject.baseChangeArrow
    {S S' : Scheme.{u}} (g : S' ⟶ S) (X : FourierMukaiObject S) :
    (FourierMukaiObject.baseChange g X).scheme ⟶ X.scheme :=
  Limits.pullback.snd g X.hom

/-- The square defining the canonical base change is cartesian. -/
theorem FourierMukaiObject.baseChange_isPullback
    {S S' : Scheme.{u}} (g : S' ⟶ S) (X : FourierMukaiObject S) :
    IsPullback (FourierMukaiObject.baseChangeArrow g X)
      (FourierMukaiObject.baseChange g X).hom X.hom g := sorry

/-- The two legs of the product comparison satisfy the pullback compatibility equation. -/
theorem FourierMukaiObject.productComparison_condition
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X Y : FourierMukaiObject S) :
    (Limits.pullback.fst (FourierMukaiObject.baseChange g X).hom
      (FourierMukaiObject.baseChange g Y).hom ≫
        FourierMukaiObject.baseChangeArrow g X) ≫ X.hom =
        (Limits.pullback.snd (FourierMukaiObject.baseChange g X).hom
          (FourierMukaiObject.baseChange g Y).hom ≫
            FourierMukaiObject.baseChangeArrow g Y) ≫ Y.hom := sorry

/-- The product comparison map is the pullback lift induced by the two base-change projections. -/
noncomputable def FourierMukaiObject.productComparison
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X Y : FourierMukaiObject S) :
    Limits.pullback (FourierMukaiObject.baseChange g X).hom
        (FourierMukaiObject.baseChange g Y).hom ⟶
      Limits.pullback X.hom Y.hom :=
  Limits.pullback.lift
    (Limits.pullback.fst (FourierMukaiObject.baseChange g X).hom
      (FourierMukaiObject.baseChange g Y).hom ≫
        FourierMukaiObject.baseChangeArrow g X)
    (Limits.pullback.snd (FourierMukaiObject.baseChange g X).hom
      (FourierMukaiObject.baseChange g Y).hom ≫
        FourierMukaiObject.baseChangeArrow g Y)
    (FourierMukaiObject.productComparison_condition g X Y)

/-- The derived pullback map on Fourier--Mukai kernel classes. -/
noncomputable def FourierMukaiObject.mapKernel
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X Y : FourierMukaiObject S) (K : fourierMukaiHom X Y) :
    fourierMukaiHom (FourierMukaiObject.baseChange g X)
      (FourierMukaiObject.baseChange g Y) :=
  (Functor.isoClassesMap
      (RingedSpace.modulePullbackPerfect
        ((FourierMukaiObject.productComparison g X Y).toLRSHom.toShHom))) K

/-- Derived pullback sends the canonical diagonal identity kernel to the diagonal identity kernel. -/
theorem FourierMukaiObject.mapKernel_id
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X : FourierMukaiObject S) :
    FourierMukaiObject.mapKernel g X X (𝟙 X) =
      𝟙 (FourierMukaiObject.baseChange g X) := sorry

/-- Derived pullback preserves convolution of Fourier--Mukai kernels. -/
theorem FourierMukaiObject.mapKernel_comp
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    {X Y Z : FourierMukaiObject S}
    (f : fourierMukaiHom X Y) (h : fourierMukaiHom Y Z) :
    FourierMukaiObject.mapKernel g X Z (FourierMukaiObject.derivedConvolution f h) =
      FourierMukaiObject.derivedConvolution
        (FourierMukaiObject.mapKernel g X Y f)
        (FourierMukaiObject.mapKernel g Y Z h) := sorry
