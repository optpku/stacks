module

public import stacks_project.Chap103.Lemma_103_8_3_Comparison
public import stacks_project.Chap103.Lemma_103_8_3_Restriction

/-!
# Lemma 103.8.3

Higher direct images of `LQCoh^{fbc}` along a quasi-compact quasi-separated
morphism of algebraic stacks representable by algebraic spaces may be computed
after restriction to the small étale site of an object of the target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver.HigherDirectImageRestriction
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 103.8.3: if `f : X ⟶ Y` is a quasi-compact quasi-separated morphism of
algebraic stacks representable by algebraic spaces and `F` lies in
`LQCoh^{fbc}(𝒪_X)`, then for an object `y` of `Y` one has
`(R^i f_* F)|_{V_étale} = R^i f'_small,* (F|_{U_étale})`, where
`f' : U = V ×_Y X ⟶ V` is the base change of `f` and `V = p(y)`. -/
@[stacks 0GQH]
theorem moduleHigherDirectImage_restrictSmallEtale
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F]
    (y : Y.total) (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f)
    (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
      (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (sliceHom y) f)
    (i : ℕ) : IsIso (comparison f y U fU eU h_fst F i) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
