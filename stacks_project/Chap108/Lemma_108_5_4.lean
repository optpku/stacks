/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_5_4_Map

/-!
# Lemma 108.5.4

An affine quasi-finite morphism of separated finite-presentation algebraic
spaces over `B` induces a morphism of Grothendieck Quot functors by fibrewise
pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Lemma 108.5.4: if `π : X ⟶ Y` is an affine quasi-finite morphism of
algebraic spaces which are separated and of finite presentation over an
algebraic space `B`, and `F` is a quasi-coherent `𝒪_X`-module, then `π_*`
induces a morphism `map π y F : quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F)`
of functors of points. -/
@[stacks 0DP1]
def map (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent] :
    quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F) :=
  pushforwardHom π y F

/-- The source-facing morphism is `pushforwardHom`. -/
theorem map_eq (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent] :
    map π y F = pushforwardHom π y F :=
  sorry

/-- The component of `map` at a test scheme sends the class of `F_T ⟶ Q` to the
class of `(π_* F)_T ⟶ π_{T,*} Q` after the canonical affine identification
`(π_* F)_T ≅ π_{T,*} F_T`. -/
theorem map_app (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent]
    (σ : (SchemesOver B)ᵒᵖ) :
    (map π y F).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map
          (fun Q : QuotPoint (π ≫ y) F σ.unop ↦ QuotPoint.pushforward π y Q)
          (Rel_pushforward π y F σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
