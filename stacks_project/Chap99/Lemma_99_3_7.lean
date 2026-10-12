/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Lemma_67_20_6
public import stacks_project.Chap69.Lemma_69_11_1_AffineBaseChange
public import stacks_project.Chap99.«99_3_1_1»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 99.3.7: if `i : X' ⟶ X` is a closed immersion of algebraic spaces over `B`,
`F` is a quasi-coherent `𝒪_X`-module, and `G'` is a quasi-coherent `𝒪_{X'}`-module,
then `Hom(F, i_* G')` and `Hom(i^* F, G')` are canonically identified as functors on
`(Sch/B)`. -/
@[stacks 08K5]
theorem homFunctor_closedImmersion {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (f : X ⟶ B) (f' : X' ⟶ B) (i : X' ⟶ X) (h_over : i ≫ f = f')
    [IsClosedImmersion i] (F : X.Modules) (G' : X'.Modules)
    [F.IsQuasicoherent] [G'.IsQuasicoherent] :
    IsIsomorphic (homFunctor f F ((pushforward i).obj G'))
      (homFunctor f' ((pullback i).obj F) G') :=
  sorry

/-- Pointwise form of the closed-immersion identification of Hom functors: at a scheme
over `B`, the two base-changed Hom-types are equivalent. -/
theorem homFunctor_closedImmersion_obj {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (f : X ⟶ B) (f' : X' ⟶ B) (i : X' ⟶ X) (h_over : i ≫ f = f')
    [IsClosedImmersion i] (F : X.Modules) (G' : X'.Modules)
    [F.IsQuasicoherent] [G'.IsQuasicoherent] (σ : SchemeOver B) :
    Nonempty
      ((baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom ((pushforward i).obj G')) ≃
        (baseChangeModule f' σ.hom ((pullback i).obj F) ⟶ baseChangeModule f' σ.hom G')) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
