/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap75.Lemma_75_5_6_Tensor
public import stacks_project.Chap75.Remark_75_6_3
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward
public import stacks_project.Chap75.Lemma_75_6_4_Pushforward

/-!
# Affine projection formula on algebraic spaces

For an affine morphism of algebraic spaces, derived pushforward after derived
pullback of a complex with quasi-coherent cohomology is isomorphic to derived
tensor with the underived direct image of the structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The underived direct image `f_* 𝒪_X`, placed in degree zero, has quasi-coherent
cohomology for a quasi-compact, quasi-separated morphism of algebraic spaces. -/
theorem pushforwardStructureSheaf_mem (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    derivedQuasiCoherentModuleProperty Y
      ((DerivedCategory.singleFunctor (Modules Y) 0).obj
        (pushforwardStructureModule f)) :=
  sorry

/-- The underived direct image `f_* 𝒪_X`, placed in degree zero as a derived module
with quasi-coherent cohomology. -/
noncomputable def pushforwardStructureSheaf (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : DerivedQCoh Y :=
  ⟨(DerivedCategory.singleFunctor (Modules Y) 0).obj
      (pushforwardStructureModule f),
    pushforwardStructureSheaf_mem f⟩

/-- The underlying derived module of `pushforwardStructureSheaf f` is the underived
direct image `f_* 𝒪_X`, placed in degree zero. -/
@[simp]
theorem pushforwardStructureSheaf_obj (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardStructureSheaf f).obj =
      (DerivedCategory.singleFunctor (Modules Y) 0).obj
        (pushforwardStructureModule f) :=
  sorry

/-- For an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`, derived
pushforward after derived pullback of `E` is isomorphic to `E` derived-tensored
with the underived direct image `f_* 𝒪_X`. -/
theorem affinePushforwardPullback_isomorphic (f : X ⟶ Y) [Affine f]
    (E : DerivedQCoh Y) :
    IsIsomorphic ((pushforward f).obj ((pullback f).obj E))
      (tensorObj E (pushforwardStructureSheaf f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
