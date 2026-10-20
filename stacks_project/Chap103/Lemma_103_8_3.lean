module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap103.Lemma_103_6_2
public import stacks_project.Chap103.Lemma_103_8_3_LiftedCFG
public import stacks_project.Chap103.Lemma_103_8_3_LiftedSmallDirect
public import stacks_project.Chap103.Lemma_103_8_3_LiftedComparison
public import stacks_project.Chap103.Lemma_103_8_3_LiftCompatibility
public import stacks_project.Chap103.Lemma_103_8_3_LiftedScheme
public import stacks_project.Chap103.Lemma_103_8_3_LiftedRestriction
public import stacks_project.Chap103.Lemma_103_8_3_Comparison
public import stacks_project.Chap103.Lemma_103_8_3_Restriction

/-! # Lemma 103.8.3

For a quasi-compact quasi-separated morphism of algebraic stacks representable
by algebraic spaces, the small-étale restriction of `R^i f_* F` at an object
`y` of `Y` agrees with the small-étale higher direct image of `F|_{U_étale}`
along the representing base change `f' : U ⟶ V`.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids
open Scheme
open scoped Bicategory
noncomputable section
universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `AlgebraicSpace.Modules.higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `rightDerived`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 103.8.3: if `f : X ⟶ Y` is a quasi-compact quasi-separated morphism of
algebraic stacks representable by algebraic spaces and `F` lies in
`LQCoh^{fbc}(𝒪_X)`, then for an object `y : V → Y` of `Y` one has
`(R^i f_* F)|_{V_étale} = R^i f'_small,* (F|_{U_étale})`, where
`f' : U = V ×_Y X ⟶ V` is the base change of `f`.
The left side is `(restrictModulesToSmallEtale Y y).obj (moduleHigherDirectImage f F i)`
in `RingedSite.ModuleCat.{u} (Etale.Small.ringedSite (Y.p.obj y).left)`.
The right side is the image of
`AlgebraicSpace.Modules.higherDirectImage fU ((restrictToU f y U eU).obj F) i`
under `(schemeEtaleRingedHom (Y.p.obj y)).modulePushforward`. -/
@[stacks 0GQH]
theorem moduleHigherDirectImage_restrictSmallEtale
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F]
    (y : Y.total) (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (moduleSliceHom y) f)
    (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
      (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (moduleSliceHom y) f)
    [Abelian U.Modules] [Abelian (AlgebraicSpace.ofOver (Y.p.obj y)).Modules]
    [HasInjectiveResolutions U.Modules] (i : ℕ) :
    IsIsomorphic
      ((restrictModulesToSmallEtale Y y).obj (moduleHigherDirectImage f F i) :
        RingedSite.ModuleCat.{u} (Etale.Small.ringedSite (Y.p.obj y).left))
      (((AlgebraicSpace.schemeEtaleRingedHom (Y.p.obj y)).modulePushforward.{u}).obj
        (AlgebraicSpace.Modules.higherDirectImage fU
          ((HigherDirectImageRestriction.restrictToU f y U eU).obj F) i)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
