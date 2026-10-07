module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of versality along a Yoneda morphism

In the setup of Definition 98.12.2, if the diagonal of `X` is representable by
algebraic spaces and locally of finite type and `X` has (RS), then versality of
`x` at a finite type point `u0` is preserved under 2-fibre product with a
Yoneda morphism from a locally finite type scheme: the representing algebraic
space is smooth over that scheme at every finite type point lying over `u0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The algebraic space `Z` over `S`, together with morphisms `toV` and `toU`,
represents the 2-fibre product of the 2-Yoneda 1-morphisms of `y` and `x`. -/
def representsYonedaFibreProduct {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU)
    {V : Scheme.{u}} (hV : V ⟶ S) (y : X.total) (hy : X.p.obj y = Over.mk hV)
    (Z : AlgebraicSpace S) (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU)) : Prop :=
  ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u}
      (yonedaOfObject hV y hy) (yonedaOfObject hU x hx) ≌
      Z.toGroupoids,
    Nonempty
        (e.hom ≫ AlgebraicSpace.toGroupoids.map toV ≫
            (AlgebraicSpace.ofOverSliceEquiv (Over.mk hV)).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u}
            (yonedaOfObject hV y hy) (yonedaOfObject hU x hx)) ∧
      Nonempty
        (e.hom ≫ AlgebraicSpace.toGroupoids.map toU ≫
            (AlgebraicSpace.ofOverSliceEquiv (Over.mk hU)).hom ≅
          TwoFibreProduct.snd.{u + 1, u, u + 1, u}
            (yonedaOfObject hV y hy) (yonedaOfObject hU x hx))

/-- Unfolding `representsYonedaFibreProduct` recovers a shared equivalence of
the Yoneda 2-fibre product with `Z.toGroupoids` and both projection triangles. -/
theorem representsYonedaFibreProduct_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU)
    {V : Scheme.{u}} (hV : V ⟶ S) (y : X.total) (hy : X.p.obj y = Over.mk hV)
    (Z : AlgebraicSpace S) (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU)) :
    representsYonedaFibreProduct hU x hx hV y hy Z toV toU ↔
      ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u}
          (yonedaOfObject hV y hy) (yonedaOfObject hU x hx) ≌
          Z.toGroupoids,
        Nonempty
            (e.hom ≫ AlgebraicSpace.toGroupoids.map toV ≫
                (AlgebraicSpace.ofOverSliceEquiv (Over.mk hV)).hom ≅
              TwoFibreProduct.fst.{u + 1, u, u + 1, u}
                (yonedaOfObject hV y hy) (yonedaOfObject hU x hx)) ∧
          Nonempty
            (e.hom ≫ AlgebraicSpace.toGroupoids.map toU ≫
                (AlgebraicSpace.ofOverSliceEquiv (Over.mk hU)).hom ≅
              TwoFibreProduct.snd.{u + 1, u, u + 1, u}
                (yonedaOfObject hV y hy) (yonedaOfObject hU x hx)) :=
  sorry

/-- A representing pair of projections yields `RepresentsBaseChange` for the
Yoneda 1-morphism of `x` along the Yoneda 1-morphism of `y`. -/
theorem representsYonedaFibreProduct.representsBaseChange
    {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S)
    (x : X.total) (hx : X.p.obj x = Over.mk hU) {V : Scheme.{u}} (hV : V ⟶ S)
    (y : X.total) (hy : X.p.obj y = Over.mk hV) (Z : AlgebraicSpace S)
    (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU))
    (hZ : representsYonedaFibreProduct hU x hx hV y hy Z toV toU) :
    RepresentsBaseChange (yonedaOfObject hU x hx) (yonedaOfObject hV y hy)
      Z toV :=
  sorry

/-- Lemma 98.12.6: let `S`, `X`, `U`, `x`, `u0` be as in Definition 98.12.2.
Assume the diagonal `Δ : X ⟶ X × X` is representable by algebraic spaces and
locally of finite type (for example if `X` is limit preserving, see
Lemma 98.11.4), and that `X` has (RS). Let `V` be a scheme locally of finite
type over `S` and let `y` be an object of `X` over `V`. Let `Z` be an algebraic
space representing the 2-fibre product of the 2-Yoneda 1-morphisms of `y` and
`x`, with projections `toV : Z ⟶ ofOver V` and `toU : Z ⟶ ofOver U`. If `z0`
is a finite type point of `Z` lying over `u0` and `x` is versal at `u0`, then
`toV` is smooth at `z0`. -/
@[stacks 0CXM]
theorem smoothAt_baseChange_of_isVersalAt {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [HasRimSchlessinger X]
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_lft : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {V : Scheme.{u}} (hV : V ⟶ S) [LocallyOfFiniteType hV] (y : X.total)
    (hy : X.p.obj y = Over.mk hV) (Z : AlgebraicSpace S)
    (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU))
    (hZ : representsYonedaFibreProduct hU x hx hV y hy Z toV toU)
    (z0 : AlgebraicSpace.Points Z) (hz0 : AlgebraicSpace.IsFiniteTypePoint z0)
    (h_over : AlgebraicSpace.Points.map toU z0 =
      AlgebraicSpace.ofOver.pointsEquiv (Over.mk hU) u0) :
    AlgebraicSpace.SmoothAt toV z0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver
