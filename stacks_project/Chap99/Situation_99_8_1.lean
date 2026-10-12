/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap99.«99_7_1_2_Functor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Situation 99.8.1 (1): let `S` be a scheme, let `f : X ⟶ B` be a morphism of
finite presentation of algebraic spaces over `S`, and let `F` be a quasi-coherent
`𝒪_X`-module. For a scheme `T` over `B`, write `X_T = X ×_B T` and write `F_T`
for the pullback of `F` along the projection `X_T ⟶ X`. The Quot functor
`Quot_{F/X/B}` sends `T` to the set of kernel-identified quotients `F_T ⟶ Q`
on `X_T` with `Q` quasi-coherent of finite presentation, flat over `T`, and with
support proper over `T`. -/
@[stacks 09TR] #check AlgebraicGeometry.AlgebraicSpace.Quot.quot

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace QuotPoint

/-- Forget proper support, sending a Quot-point to the underlying finitely
presented quotient point of `Q^{fp}_{F/X/B}`. -/
def toFpPoint {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) : FpPoint f F σ where
  point := Q.point
  isFinitePresentation := Q.isFinitePresentation

/-- `toFpPoint` keeps the same underlying quotient morphism. -/
theorem toFpPoint_spec {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toFpPoint.point = Q.point := sorry

end QuotPoint

/-- Kernel identification of Quot-points is preserved by `toFpPoint`. -/
theorem toFpPoint_rel (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f F σ),
      (quotSetoid f F σ).r Q₁ Q₂ →
        (fpSetoid f F σ).r Q₁.toFpPoint Q₂.toFpPoint := sorry

/-- Situation 99.8.1 (2): by Derived Categories of Spaces, Lemma 75.7.8, the
Quot functor `Quot_{F/X/B}` is a subfunctor of `Q^{fp}_{F/X/B}`. -/
@[stacks 09TR]
def quotFpι (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : quot f F ⟶ fpFunctor f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.toFpPoint)
        (toFpPoint_rel f F σ.unop))
  naturality := sorry

/-- The inclusion of Quot-classes into `Q^{fp}_{F/X/B}` is the setoid map
induced by `QuotPoint.toFpPoint`. -/
theorem quotFpι_app (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (σ : (SchemesOver B)ᵒᵖ) :
    (quotFpι f F).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.toFpPoint)
          (toFpPoint_rel f F σ.unop)) := sorry

/-- The inclusion of `Quot_{F/X/B}` into `Q_{F/X/B}` factors through
`Q^{fp}_{F/X/B}`. -/
theorem quotι_eq_quotFpι_comp_fpι (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] :
    quotι f F = quotFpι f F ≫ fpι f F := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
