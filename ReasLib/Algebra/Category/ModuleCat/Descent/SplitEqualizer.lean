/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Retraction
public import ReasLib.Algebra.Category.ModuleCat.Descent.BaseExtension
public import ReasLib.Algebra.Category.ModuleCat.Descent.Diagram
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The split equalizer attached to module descent data

This file gives names to the three additive maps in the descent equalizer and to the two
tensor-multiplication retractions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat.DescentData.SplitEqualizer

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

open ChangeOfRings

/-- The unique module component of a descent datum along `algebraMap R S`. -/
abbrev component (D : ModuleCat.DescentData (algebraMap R S)) : ModuleCat.{u} S :=
  D.obj PUnit.unit

/-- The zeroth coface `S ⟶ S ⊗[R] S`, inserting `1` on the left. -/
def squareZero (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    S →+* S ⊗[R] S :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The first coface `S ⟶ S ⊗[R] S`, inserting `1` on the right. -/
def squareOne (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    S →+* S ⊗[R] S :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The zeroth coface from the tensor square to the left-associated tensor cube. -/
def cubeZero (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    S ⊗[R] S →+* (S ⊗[R] S) ⊗[R] S :=
  (Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id R S)).toRingHom

/-- The first coface from the tensor square to the left-associated tensor cube. -/
def cubeOne (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    S ⊗[R] S →+* (S ⊗[R] S) ⊗[R] S :=
  (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) (AlgHom.id R S)).toRingHom

/-- The second coface from the tensor square to the left-associated tensor cube. -/
def cubeTwo (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    S ⊗[R] S →+* (S ⊗[R] S) ⊗[R] S :=
  Algebra.TensorProduct.includeLeftRingHom

/-- Multiplication of the first two tensor factors,
`σ₀¹ : (S ⊗[R] S) ⊗[R] S ⟶ S ⊗[R] S`. -/
def sigmaOne (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (S ⊗[R] S) ⊗[R] S →+* S ⊗[R] S :=
  (Algebra.TensorProduct.map (Algebra.TensorProduct.lmul' R) (AlgHom.id R S)).toRingHom

/-- The formula `σ₀¹((a₀ ⊗ₜ a₁) ⊗ₜ a₂) = a₀ * a₁ ⊗ₜ a₂`. -/
theorem sigmaOne_tmul (a₀ a₁ a₂ : S) :
    sigmaOne R S ((a₀ ⊗ₜ[R] a₁) ⊗ₜ[R] a₂) =
      (a₀ * a₁) ⊗ₜ[R] a₂ := sorry

/-- Multiplication retracts the first coface of the tensor square. -/
theorem tensorSquareMultiplication_comp_squareOne :
    (Algebra.tensorSquareMultiplication R S).comp (squareOne R S) =
      RingHom.id S := sorry

/-- Multiplication of the first two factors retracts the middle coface of the tensor cube. -/
theorem sigmaOne_comp_cubeOne :
    (sigmaOne R S).comp (cubeOne R S) =
      RingHom.id (S ⊗[R] S) := sorry

/-- The zeroth cube coface after the first square coface is the middle base leg. -/
theorem middleCoface :
    (cubeZero R S).comp (squareOne R S) =
      (cubeTwo R S).comp (squareZero R S) := sorry

/-- The first and second cube cofaces agree after the first square coface. -/
theorem firstCoface :
    (cubeOne R S).comp (squareOne R S) =
      (cubeTwo R S).comp (squareOne R S) := sorry

/-- The two tensor-square legs define the same map to the base of the descent family. -/
theorem squareLegs_overBase :
    (CommRingCat.ofHom (squareOne R S)).op ≫
        (CommRingCat.ofHom (algebraMap R S)).op =
      (CommRingCat.ofHom (squareZero R S)).op ≫
        (CommRingCat.ofHom (algebraMap R S)).op := sorry

/-- The two tensor-cube legs used in the equalizer define the same map to the base. -/
theorem cubeLegs_overBase :
    (CommRingCat.ofHom
        ((cubeOne R S).comp (squareOne R S))).op ≫
        (CommRingCat.ofHom (algebraMap R S)).op =
      (CommRingCat.ofHom
        ((cubeZero R S).comp (squareOne R S))).op ≫
        (CommRingCat.ofHom (algebraMap R S)).op := sorry

/-- The transition isomorphism of `D` over the two cofaces of the tensor square. -/
def squareIso (D : ModuleCat.DescentData (algebraMap R S)) :
    ModuleCat.ExtendScalars.obj' (squareZero R S) (component D) ≅
      ModuleCat.ExtendScalars.obj' (squareOne R S) (component D) :=
  D.iso
    ((CommRingCat.ofHom ((squareZero R S).comp (algebraMap R S))).op)
    ((CommRingCat.ofHom (squareZero R S)).op)
    ((CommRingCat.ofHom (squareOne R S)).op)
    rfl squareLegs_overBase

/-- The transition isomorphism of `D` between the middle and first tensor-cube legs. -/
def cubeIso (D : ModuleCat.DescentData (algebraMap R S)) :
    ModuleCat.ExtendScalars.obj'
        ((cubeZero R S).comp (squareOne R S))
        (component D) ≅
      ModuleCat.ExtendScalars.obj'
        ((cubeOne R S).comp (squareOne R S))
        (component D) :=
  D.iso
    ((CommRingCat.ofHom
      (((cubeZero R S).comp (squareOne R S)).comp
        (algebraMap R S))).op)
    ((CommRingCat.ofHom
      ((cubeZero R S).comp (squareOne R S))).op)
    ((CommRingCat.ofHom
      ((cubeOne R S).comp (squareOne R S))).op)
    rfl cubeLegs_overBase

/-- Comparison from the direct middle tensor-cube extension to iterated extension along
`squareZero R S` and `cubeTwo R S`. -/
def middleComparison (D : ModuleCat.DescentData (algebraMap R S)) :
    ModuleCat.ExtendScalars.obj'
        ((cubeZero R S).comp (squareOne R S)) (component D) ≅
      ModuleCat.ExtendScalars.obj' (cubeTwo R S)
        (ModuleCat.ExtendScalars.obj' (squareZero R S) (component D)) :=
  (eqToIso (congrArg (fun φ ↦ ModuleCat.ExtendScalars.obj' φ (component D))
    middleCoface)).trans
      ((ModuleCat.extendScalarsComp (squareZero R S) (cubeTwo R S)).app (component D))

/-- Comparison from the direct first tensor-cube extension to iterated extension along
`squareOne R S` and `cubeTwo R S`. -/
def targetComparison (D : ModuleCat.DescentData (algebraMap R S)) :
    ModuleCat.ExtendScalars.obj'
        ((cubeOne R S).comp (squareOne R S)) (component D) ≅
      ModuleCat.ExtendScalars.obj' (cubeTwo R S)
        (ModuleCat.ExtendScalars.obj' (squareOne R S) (component D)) :=
  (eqToIso (congrArg (fun φ ↦ ModuleCat.ExtendScalars.obj' φ (component D))
    firstCoface)).trans
      ((ModuleCat.extendScalarsComp (squareOne R S) (cubeTwo R S)).app (component D))

/-- Base change of the tensor-square transition isomorphism along the second cube coface. -/
def thetaBaseChange (D : ModuleCat.DescentData (algebraMap R S)) :
    ModuleCat.ExtendScalars.obj'
        ((cubeZero R S).comp (squareOne R S)) (component D) ⟶
      ModuleCat.ExtendScalars.obj'
        ((cubeOne R S).comp (squareOne R S)) (component D) :=
  (middleComparison D).hom ≫
    ModuleCat.ExtendScalars.map' (cubeTwo R S) (squareIso D).hom ≫
    (targetComparison D).inv

/-- Pullback compatibility identifies the direct cube transition with base change of the
tensor-square transition. -/
theorem cubeIso_hom (D : ModuleCat.DescentData (algebraMap R S)) :
    (cubeIso D).hom = thetaBaseChange D := sorry

/-- The source arrow `M ⟶ M ⊗_{S,δ₁¹} S₂` of the descent equalizer. -/
def source (D : ModuleCat.DescentData (algebraMap R S)) :
    AddCommGrpCat.of (component D) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        (squareOne R S) (component D)) :=
  ModuleCat.DescentDiagram.source
    (squareZero R S) (squareOne R S) (component D) (squareIso D)

/-- The source arrow sends `m` to `squareIso D` applied to `1 ⊗ₜ m`. -/
theorem source_apply (D : ModuleCat.DescentData (algebraMap R S)) (m : component D) :
    source D m = (squareIso D).hom
      ((1 : S ⊗[R] S) ⊗ₜ[S, squareZero R S] m) := sorry

/-- The upper arrow of the parallel pair in the descent equalizer. -/
def upper (D : ModuleCat.DescentData (algebraMap R S)) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        (squareOne R S) (component D)) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        ((cubeOne R S).comp (squareOne R S))
        (component D)) :=
  ModuleCat.DescentDiagram.upper
    (squareZero R S) (squareOne R S)
    ((cubeZero R S).comp (squareOne R S))
    ((cubeOne R S).comp (squareOne R S))
    (cubeZero R S) (cubeTwo R S) (component D) (squareIso D)
    rfl middleCoface firstCoface

/-- The lower arrow of the parallel pair in the descent equalizer. -/
def lower (D : ModuleCat.DescentData (algebraMap R S)) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        (squareOne R S) (component D)) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        ((cubeOne R S).comp (squareOne R S))
        (component D)) :=
  ModuleCat.DescentDiagram.lower
    (squareOne R S) ((cubeOne R S).comp (squareOne R S))
    (cubeOne R S) (component D) rfl

/-- The source arrow equalizes the upper and lower arrows. -/
theorem condition (D : ModuleCat.DescentData (algebraMap R S)) :
    source D ≫ upper D = source D ≫ lower D := sorry

/-- The retraction of the source arrow induced by tensor-square multiplication. -/
def leftRetraction (D : ModuleCat.DescentData (algebraMap R S)) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        (squareOne R S) (component D)) ⟶
      AddCommGrpCat.of (component D) :=
  ModuleCat.ExtendScalars.addRetraction (squareOne R S)
    (Algebra.tensorSquareMultiplication R S)
    tensorSquareMultiplication_comp_squareOne (component D)

/-- The left retraction sends `x ⊗ₜ m` to the product of `x` acting on `m`. -/
theorem leftRetraction_tmul (D : ModuleCat.DescentData (algebraMap R S))
    (x : S ⊗[R] S) (m : component D) :
    leftRetraction D (x ⊗ₜ[S, squareOne R S] m) =
      Algebra.tensorSquareMultiplication R S x • m := sorry

/-- The retraction `1_M ⊗ σ₀¹` of the lower parallel arrow. -/
def rightRetraction (D : ModuleCat.DescentData (algebraMap R S)) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        ((cubeOne R S).comp (squareOne R S))
        (component D)) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj'
        (squareOne R S) (component D)) :=
  (forget₂ (ModuleCat ((S ⊗[R] S) ⊗[R] S)) AddCommGrpCat).map
      ((ModuleCat.extendScalarsComp (squareOne R S)
        (cubeOne R S)).hom.app (component D)) ≫
    ModuleCat.ExtendScalars.addRetraction (cubeOne R S)
      (sigmaOne R S) sigmaOne_comp_cubeOne
      (ModuleCat.ExtendScalars.obj' (squareOne R S) (component D))

/-- The right retraction applies `σ₀¹` to the tensor-cube scalar. -/
theorem rightRetraction_tmul (D : ModuleCat.DescentData (algebraMap R S))
    (x : (S ⊗[R] S) ⊗[R] S) (m : component D) :
    rightRetraction D
        (x ⊗ₜ[S, (cubeOne R S).comp
          (squareOne R S)] m) =
      sigmaOne R S x ⊗ₜ[S, squareOne R S] m := sorry

/-- The source arrow followed by the tensor-square multiplication retraction is the identity. -/
theorem source_leftRetraction (D : ModuleCat.DescentData (algebraMap R S)) :
    source D ≫ leftRetraction D = 𝟙 _ := sorry

/-- The lower arrow followed by `1_M ⊗ σ₀¹` is the identity. -/
theorem lower_rightRetraction (D : ModuleCat.DescentData (algebraMap R S)) :
    lower D ≫ rightRetraction D = 𝟙 _ := sorry

/-- The cocycle identity gives compatibility of the upper arrow with the two retractions. -/
theorem upper_rightRetraction (D : ModuleCat.DescentData (algebraMap R S)) :
    upper D ≫ rightRetraction D = leftRetraction D ≫ source D := sorry

/-- The descent diagram equipped with its tensor-multiplication splitting. -/
def splitting (D : ModuleCat.DescentData (algebraMap R S)) :
    CategoryTheory.IsSplitEqualizer (upper D) (lower D) (source D) where
  leftRetraction := leftRetraction D
  rightRetraction := rightRetraction D
  condition := condition D
  ι_leftRetraction := source_leftRetraction D
  bottom_rightRetraction := lower_rightRetraction D
  top_rightRetraction := upper_rightRetraction D

/-- The equalizer universal property canonically induced by the chosen splitting. -/
def isLimit (D : ModuleCat.DescentData (algebraMap R S)) :
    Limits.IsLimit (splitting D).asFork :=
  (splitting D).isEqualizer

end ModuleCat.DescentData.SplitEqualizer
