module

public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction

/-!
# Relative normalization of algebraic spaces

Typed compatibility checks for the relative spectrum of the integral-closure algebra,
its two canonical maps, and their factorization identity.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

#check (Hom.normalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    AlgebraicSpace S)

#check (Hom.normalization_eq_relativeSpec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.normalization f = relativeSpec (integralClosureAlgebra f))

#check (Hom.fromNormalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.normalization f ⟶ Y)

#check (Hom.fromNormalization_eq_relativeSpecπ :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.fromNormalization f = relativeSpecπ (integralClosureAlgebra f))

#check (Hom.fromNormalization_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (p : relativeSpectrumPair (integralClosureAlgebra f) T.unop),
    (Hom.fromNormalization f).app T p = p.1)

#check (Hom.toNormalizationAlgebraMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {T : Over S} (t : ofOver T ⟶ X),
    (integralClosureAlgebra f).obj ⟶ relativeSpectrumTarget (t ≫ f))

#check (Hom.toNormalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    X ⟶ Hom.normalization f)

#check (Hom.toNormalization_app_toX :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T),
    ((Hom.toNormalization f).app T x).1 =
      yonedaEquiv ((yonedaEquiv.symm x ≫ f : yoneda.obj T.unop ⟶ Y.functorOfPoints)))

#check (Hom.toNormalization_fromNormalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.toNormalization f ≫ Hom.fromNormalization f = f)

end AlgebraicGeometry.AlgebraicSpace
