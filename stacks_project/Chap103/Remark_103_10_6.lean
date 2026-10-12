/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Remark_103_10_6_Tensor
public import stacks_project.Chap103.Remark_103_10_6_Sheafification
public import stacks_project.Chap103.Remark_103_10_6_SiteSheafification
public import stacks_project.Chap103.Lemma_103_10_4

/-!
# Tensor-preservation of the quasi-coherent adjunction

On an algebraic stack, tensor-closure of `QCoh` and of `LQCoh^{fbc}` makes the
inclusions `QCoh ⥤ LQCoh^{fbc} ⥤ Mod` preserve tensor. The right adjoint
`Q = LQCohFbc.toQCoh` is likewise strong on tensor: its tensorator is an
isomorphism because it becomes one after restriction to `U_étale` for every
flat `U ⟶ X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids Functor.Fiber

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Remark 103.10.6 (1): on an algebraic stack `X`, the inclusion
`QCoh.toLQCohFbc : QCoh X ⥤ LQCohFbc X` is strong on tensor:
`i(F) ⊗ i(G) ≅ i(F ⊗ G)` in `LQCoh^{fbc}`, where the left-hand tensor is
the étale tensor. -/
@[stacks 0GQM, instance]
instance QCoh.toLQCohFbc_tensorator_isIso {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    IsIso (QCoh.toLQCohFbc_tensorator F G) :=
  sorry

/-- Remark 103.10.6 (2): the right adjoint `Q = LQCohFbc.toQCoh` is strong
on tensor: the tensorator `μ : Q(F) ⊗ Q(G) ⟶ Q(F ⊗ G)` is an isomorphism. -/
@[stacks 0GQM, instance]
instance LQCohFbc.toQCoh_μ_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    IsIso (LQCohFbc.toQCoh_μ adj F G) :=
  sorry

/-- Characterisation of `μ` by the source triangle
`i(μ) ≫ ε_{F ⊗ G} = (oplax i-tensorator) ≫ (ε_F ⊗ ε_G)`. -/
theorem LQCohFbc.toQCoh_μ_counit_triangle {X : GroupoidsOver S}
    [AlgebraicStack X] (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X)
    (F G : LQCohFbc X) :
    (QCoh.toLQCohFbc X).map (LQCohFbc.toQCoh_μ adj F G) ≫
        adj.counit.app (LQCohFbc.ofModuleTensorEtale F G) =
      LQCohFbc.toQCoh_μ_pre adj F G :=
  by
    exact (adj.homEquiv _ _).symm_apply_apply (LQCohFbc.toQCoh_μ_pre adj F G)

/-- Restriction of the i-tensorator `i(QF) ⊗ i(QG) ⟶ i(QF ⊗ QG)` to the small
étale site of a flat object is an isomorphism. -/
theorem QCoh.toLQCohFbc_tensorator_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (F G : QCoh X) :
    IsIso
      ((restrictModulesToSmallEtale X (fiberInclusion.obj x)).map
        (QCoh.toLQCohFbc_tensorator_hom F G)) :=
  sorry

/-- Restriction of `ε_F ⊗ ε_G` to the small étale site of a flat object is an
isomorphism. -/
theorem LQCohFbc.tensorCounit_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    IsIso
      ((restrictModulesToSmallEtale X (fiberInclusion.obj x)).map
        ((LQCohFbc.inclusion X).map (LQCohFbc.tensorCounit adj F G))) :=
  sorry

/-- Restriction of `μ` to the small étale site of a flat object is an
isomorphism, so Lemma 103.4.2 applies. -/
theorem LQCohFbc.toQCoh_μ_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    IsIso
      ((QCoh.restrictToSmallEtaleViaRestriction X
          (fiberInclusion.obj x)).map
        (LQCohFbc.toQCoh_μ adj F G)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
