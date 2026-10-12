/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Span.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap106.Lemma_106_16_2_Algebra

/-!
# Universal injectivity of the tensor-functor algebra map

If `X` is Noetherian and `g : U ⟶ X` is surjective and flat, with notation as
in Lemma 106.16.2, the `B`-linear structure map `B → C` is universally
injective.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The `B`-linear structure map `B →ₗ[B] C` sending `b` to `b • 1`, where
`C = F(g_{QCoh,*} O_U)`. -/
def algebraLinearMap {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {B : Type u} [CommRing B] (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    B →ₗ[B] (algebraModule F g : Type u) :=
  LinearMap.toSpanSingleton B (algebraModule F g : Type u) (algebraOne F h_unit g)

/-- `algebraLinearMap` evaluates as scalar multiplication of the unit of `C`. -/
theorem algebraLinearMap_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (b : B) :
    algebraLinearMap F h_unit g b = b • algebraLinearMap F h_unit g 1 :=
  sorry

/-- The unit of `algebraLinearMap` is `algebraOne`. -/
theorem algebraLinearMap_one {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    algebraLinearMap F h_unit g 1 = algebraOne F h_unit g :=
  sorry

/-- Lemma 106.16.3. Notation as in Lemma 106.16.2. Assume `X` is Noetherian and
`g` is surjective and flat. Then the structure map `B → C` is universally
injective as a map of `B`-modules. -/
@[stacks 0GRL]
theorem algebraMap_universallyInjective
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsNoetherian X]
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
    [AlgebraicStack.Surjective g] [AlgebraicStack.Flat g] :
    LinearMap.UniversallyInjective.{u, u, u, u} (algebraLinearMap F h_unit g) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
