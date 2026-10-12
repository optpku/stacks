/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Relative normalization of algebraic spaces

For a qcqs morphism `f : X ⟶ Y` of algebraic spaces, the normalization of `Y` in `X` is the
relative spectrum of the integral closure of `𝒪_Y` in `f_* 𝒪_X`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

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

/-- `fromNormalization f` is the structure morphism of the relative spectrum of `O'`. -/
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

/-- Evaluation of `f_* 𝒪_X` at a test map `t : T ⟶ X`, as a morphism of `𝒪_Y`-algebras into
`(t ≫ f)_* 𝒪_T`. -/
def Hom.toNormalizationAlgebraMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {T : Over S} (t : ofOver T ⟶ X) :
    (integralClosureAlgebra f).obj ⟶ relativeSpectrumTarget (t ≫ f) :=
  ((QcAlgebraUnder.forget Y).map (integralClosureAlgebra_inclusion f)) ≫
    Under.homMk
      ((commRingPushforward f).map (commRingStructureSheafMap t) ≫
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
