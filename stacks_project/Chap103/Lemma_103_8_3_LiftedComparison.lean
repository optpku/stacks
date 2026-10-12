/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap103.Lemma_103_8_3_Comparison

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.HigherDirectImageComparison

/-- Read the component at a geometric small-site comma arrow from the canonical
module pushforward, through its underlying-sheaf and right-Kan limit isomorphisms. -/
def smallEvaluation {S : Scheme.{u}} {U V : AlgebraicSpace S} (fU : U ⟶ V)
    (N : AlgebraicSpace.Modules.Lift U) (b : V.smallEtaleSite)
    (q : AlgebraicSpace.compareSmallIndex fU b)
    (x : ((AlgebraicSpace.Modules.pushforwardLift fU).obj N).val.obj (op b)) :=
  let Q := (CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
    (AlgebraicSpace.commRingedSiteLift U).structureSheaf).obj N
  let v := op ((AlgebraicSpace.etaleBaseChange fU).obj b)
  let i := AlgebraicSpace.smallEtaleInclusion U
  let k := ((RingedSite.ToposHom.ModulePushforward.forgetIso
    (AlgebraicSpace.ringedToposHomLift fU)).hom.app N).hom.app (op b)
  let t := (i.op.ranObjObjIsoLimit Q.obj v).hom ≫
    limit.π (StructuredArrow.proj v i.op ⋙ Q.obj) q
  t (k x)

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
variable (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
variable (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (moduleSliceHom y) f)
variable (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
    (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (moduleSliceHom y) f)

/-- The constructed comparison recovers exactly the BIG evaluation at the comma
arrow induced by the presentation and fibre-product cell. -/
theorem underivedValue_projection (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (q : AlgebraicSpace.compareSmallIndex fU b)
    (s : ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj (op b)) :
    smallEvaluation fU ((coefficient f y U eU).obj M) b q
        (underivedValue f y U fU eU h_fst M b s) =
      bigEvaluation f M
        ((toFunctor (moduleSliceHom y)).obj ((smallEtaleFunctor _ _ (eV y)).obj b))
        ((toFunctor (snd f y)).obj ((smallEtaleFunctor U _ eU).obj q.right.unop))
        (bigArrow f y U fU eU h_fst b q) s :=
  sorry

end AlgebraicGeometry.GroupoidsOver.HigherDirectImageComparison
