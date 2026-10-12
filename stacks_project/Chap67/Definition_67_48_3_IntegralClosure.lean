/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_20_10_Pushforward
public import stacks_project.Chap67.Lemma_67_48_1_IntegralClosure
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Integral closure of `𝒪_Y` in `f_* 𝒪_X`

For a quasi-compact quasi-separated morphism of algebraic spaces, the pushforward of the
commutative structure sheaf is a quasi-coherent algebra, and `integralClosureAlgebra f` is
its integral closure in the sense of `QcAlgebraUnder.integralClosure`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Pointwise limits presenting the right Kan extension of a commutative-ring presheaf along
`smallEtaleInclusion`. -/
instance smallEtaleInclusion_op_hasLimit_commRingCat (X : AlgebraicSpace S)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u}) (Y : (spacesEtaleSite X)ᵒᵖ) :
    HasLimit (StructuredArrow.proj Y (smallEtaleInclusion X).op ⋙ F) :=
  sorry

/-- The cone of global-section maps `Γ(V) ⟶ Γ(W)` presenting `𝒪_Y(V) ⟶ (f_* 𝒪_X)(V)`. -/
def commRingStructureSheafMapCone {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
        (smallEtaleInclusion X).op ⋙ (commRingStructureSheaf X).obj) where
  pt := (commRingStructureSheaf Y).obj.obj (op V)
  π :=
    { app := fun a ↦ (etaleSquareOfArrow f V a).map.left.appTop
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `V` of the direct-image structure-sheaf map `𝒪_Y ⟶ f_* 𝒪_X`. -/
def commRingStructureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : (smallEtaleSite Y)ᵒᵖ) :
    (commRingStructureSheaf Y).obj.obj V ⟶
      ((commRingPushforward f).obj (commRingStructureSheaf X)).obj.obj V :=
  commStructureSheafMap_app f V

/-- The direct-image form of `f^♯`, as a morphism of commutative-ring sheaves on `Y_étale`. -/
def commRingStructureSheafMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingStructureSheaf Y ⟶
      (commRingPushforward f).obj (commRingStructureSheaf X) :=
  InducedCategory.homMk
    { app := fun V ↦ commRingStructureSheafMap_app f V
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `commRingStructureSheafMap f` at `V` is the limit-lift comparison. -/
theorem commRingStructureSheafMap_app_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : (smallEtaleSite Y)ᵒᵖ) :
    (InducedCategory.Hom.hom (commRingStructureSheafMap f)).app V =
      commRingStructureSheafMap_app f V :=
  rfl

/-- The quasi-coherent `𝒪_Y`-algebra `f_* 𝒪_X` attached to a qcqs morphism. -/
def pushforwardStructureQcAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : Y.QcAlgebraUnder where
  obj := Under.mk (commRingStructureSheafMap f)
  property := sorry

/-- Forgetting commutativity in `pushforwardStructureQcAlgebra f` recovers the ring-valued
pushforward of `𝒪_X`. -/
theorem pushforwardStructureQcAlgebra_forget₂ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (pushforwardStructureQcAlgebra f).obj.right =
      pushforwardStructureAlgebra f :=
  sorry

/-- The sheaf of `pushforwardStructureQcAlgebra f` is the commutative-ring pushforward of
`𝒪_X`. -/
theorem pushforwardStructureQcAlgebra_sheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardStructureQcAlgebra f).obj.right =
      (commRingPushforward f).obj (commRingStructureSheaf X) :=
  rfl

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


end AlgebraicGeometry.AlgebraicSpace
