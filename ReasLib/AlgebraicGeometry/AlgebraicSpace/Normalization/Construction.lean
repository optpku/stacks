module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.IntegralClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Basic

/-!
# Relative normalization of algebraic spaces

For a quasi-compact quasi-separated morphism, the relative spectrum of the integral closure
of the target structure sheaf in the direct image of the source structure sheaf carries
a canonical factorization of the morphism.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The integral closure of `𝒪_Y` in `f_* 𝒪_X`, as a quasi-coherent `𝒪_Y`-algebra. -/
def integralClosureAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : Y.QcAlgebraUnder :=
  QcAlgebraUnder.integralClosure (pushforwardStructureQcAlgebra f)

/-- `integralClosureAlgebra f` is the integral closure of the pushforward algebra. -/
theorem integralClosureAlgebra_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    integralClosureAlgebra f =
      QcAlgebraUnder.integralClosure (pushforwardStructureQcAlgebra f) :=
  rfl

/-- The inclusion of the integral-closure algebra into `f_* 𝒪_X`. -/
def integralClosureAlgebra_inclusion {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    integralClosureAlgebra f ⟶ pushforwardStructureQcAlgebra f :=
  QcAlgebraUnder.inclusion (pushforwardStructureQcAlgebra f)

/-- The inclusion `integralClosureAlgebra f ⟶ pushforwardStructureQcAlgebra f` is the
canonical inclusion of locally integral sections. -/
theorem integralClosureAlgebra_inclusion_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    integralClosureAlgebra_inclusion f =
      QcAlgebraUnder.inclusion (pushforwardStructureQcAlgebra f) :=
  rfl

/-- The normalization of `Y` in `X` along a qcqs morphism `f : X ⟶ Y`, as the relative spectrum
of the integral closure of `𝒪_Y` in `f_* 𝒪_X`. -/
def Hom.normalization {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : AlgebraicSpace S :=
  relativeSpec (integralClosureAlgebra f)

/-- The normalization of `Y` in `X` is the relative spectrum of `integralClosureAlgebra f`. -/
theorem Hom.normalization_eq_relativeSpec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.normalization f = relativeSpec (integralClosureAlgebra f) :=
  rfl

/-- The structure morphism `ν : X' ⟶ Y` of the relative normalization. -/
def Hom.fromNormalization {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : Hom.normalization f ⟶ Y :=
  relativeSpecπ (integralClosureAlgebra f)

/-- The normalization morphism is the projection of the relative spectrum of the
integral-closure algebra. -/
theorem Hom.fromNormalization_eq_relativeSpecπ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.fromNormalization f = relativeSpecπ (integralClosureAlgebra f) :=
  rfl

/-- The component of `fromNormalization f` at `T` is the underlying map to `Y`. -/
theorem Hom.fromNormalization_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (p : relativeSpectrumPair (integralClosureAlgebra f) T.unop) :
    (Hom.fromNormalization f).app T p = p.1 :=
  rfl

/-- Inclusion and evaluation at a test map `t : T ⟶ X` send the integral-closure algebra
to the `𝒪_Y`-algebra `(t ≫ f)_* 𝒪_T`. -/
def Hom.toNormalizationAlgebraMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {T : Over S} (t : ofOver T ⟶ X) :
    (integralClosureAlgebra f).obj ⟶ relativeSpectrumTarget (t ≫ f) :=
  ((QcAlgebraUnder.forget Y).map (integralClosureAlgebra_inclusion f)) ≫
    Under.homMk
      ((commRingPushforward f).map (commStructureSheafMap t) ≫
        commRingPushforwardPrecomp t f)
      sorry

/-- The factorization map `f' : X ⟶ X'` of a qcqs morphism through its relative normalization. -/
def Hom.toNormalization {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : X ⟶ Hom.normalization f where
  app T :=
    TypeCat.ofHom fun (x : X.functorOfPoints.obj T) ↦
      relativeSpectrumPairMk (yonedaEquiv.symm x ≫ f)
        (Hom.toNormalizationAlgebraMap f (yonedaEquiv.symm x))
  naturality := sorry

/-- The component of `toNormalization f` at `T` has underlying map to `Y` equal to `f`. -/
theorem Hom.toNormalization_app_toX {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    ((Hom.toNormalization f).app T x).1 =
      yonedaEquiv ((yonedaEquiv.symm x ≫ f : yoneda.obj T.unop ⟶ Y.functorOfPoints)) :=
  sorry

/-- The canonical factorization identity `toNormalization f ≫ fromNormalization f = f`. -/
theorem Hom.toNormalization_fromNormalization {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.toNormalization f ≫ Hom.fromNormalization f = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
