/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_28_1_Comparison
public import stacks_project.Chap78.Lemma_78_28_1_InverseImage
public import stacks_project.Chap78.Lemma_78_28_1_Quotient

/-!
# Lemma 78.28.1

Change of big site for the quotient stack of a groupoid in algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u uC w

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [(slicePost ι S).IsCocontinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]
variable [HasPullbacks (Over S)] [HasEqualizers (Over S)]
variable [PreservesLimitsOfShape WalkingCospan (slicePost ι S)]
variable [PreservesLimitsOfShape WalkingParallelPair (slicePost ι S)]
variable [Small.{w} (Over (ι.obj S))]

/-- Lemma 78.28.1: suppose given big sites `Sch_fppf` and `Sch'_fppf` with `Sch_fppf`
contained in `Sch'_fppf`, and let `S` be an object of `Sch_fppf`. Let `(U, R, s, t, c)`
be a groupoid in algebraic spaces over `B` on `(Sch/S)_fppf`, and let
`f : (Sch'/S)_fppf ⟶ (Sch/S)_fppf` be the morphism of sites corresponding to the
inclusion. Then there is a canonical equivalence of stacks in groupoids over
`(Sch'/S)_fppf` between `[f⁻¹U/f⁻¹R]` and `f⁻¹[U/R]`. The displayed morphism
`quotientStackInverseImageHom` is the proof-direction functor
`f⁻¹[U/R] ⟶ [f⁻¹U/f⁻¹R]` obtained by stackifying `(T', φ, x) ↦ x ∘ φ` from
`u_p[U/_p R]`; the book arrow `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is its quasi-inverse. -/
@[stacks 04WX, instance]
instance quotientStackInverseImage_isEquivalence (G : GroupoidOnSlice ι J S) :
    (quotientStackInverseImageHom ι J S G).toBasedFunctor.IsEquivalence := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
