/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap106.Lemma_106_16_2_Algebra
public import stacks_project.Chap106.Lemma_106_16_2_Associated

/-!
# Affine evaluation of a right exact tensor functor

A right exact tensor functor on quasi-coherent modules of an algebraic stack
with affine diagonal, evaluated on the pushforward of modules from an affine
scheme, is tensoring over the resulting algebra.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- Lemma 106.16.2. Let `X` be an algebraic stack with affine diagonal. Let `B`
be a ring. Let `F : QCoh(O_X) ⥤ ModuleCat B` be a right exact tensor functor
which commutes with direct sums. Let `g : U ⟶ X` be a morphism with
`U = Spec(A)` affine. Then `C = F(g_{QCoh,*} O_U)` is a commutative `B`-algebra
and there is a ring map `A → C` such that `F ∘ g_{QCoh,*}` sends an `A`-module
`M` to `M ⊗[A] C` as a `B`-module. -/
@[stacks 0GRK]
theorem directImage_comp_iso_tensoring
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    Nonempty
      (associatedQCoh U ⋙ directImage g ⋙ F ≅
        tensoringAlong F h_tensor h_unit g) :=
  sorry

/-- `directImage_comp_iso_tensoring` identifies `F ∘ g_{QCoh,*}` of associated
`A`-modules with tensoring along `A → C`. -/
theorem directImage_comp_iso_tensoring_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    Nonempty
      ((associatedQCoh U ⋙ directImage g ⋙ F).obj M ≅
        (tensoringAlong F h_tensor h_unit g).obj M) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
