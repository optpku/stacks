module

public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 67.48.3: for a scheme `S` and a quasi-compact quasi-separated morphism
`f : Y ⟶ X` of algebraic spaces over `S`, the normalization of `X` in `Y` is the morphism
`ν = Hom.fromNormalization f : Hom.normalization f ⟶ X` over `S`, where
`Hom.normalization f` is the relative spectrum of the integral closure of `𝒪_X` in
`f_* 𝒪_Y`. The canonical map from `Y` gives a factorization of `f`. -/
@[stacks 0822] #check (AlgebraicGeometry.AlgebraicSpace.Hom.fromNormalization :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.AlgebraicSpace S} → (f : Y ⟶ X) →
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f] →
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f] →
    (AlgebraicGeometry.AlgebraicSpace.Hom.normalization f ⟶ X))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.normalization_eq_relativeSpec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.normalization f = relativeSpec (integralClosureAlgebra f))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f], Y ⟶ Hom.normalization f)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.toNormalization_fromNormalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.toNormalization f ≫ Hom.fromNormalization f = f)
