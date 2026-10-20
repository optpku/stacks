module
public import stacks_project.Chap103.Lemma_103_8_3_Comparison

@[expose] public section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.HigherDirectImageComparison
variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
variable (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
variable (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (moduleSliceHom y) f)
variable (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
    (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (moduleSliceHom y) f)

/-- Land on the existing lifted small étale ringed site of the ORIGINAL scheme. -/
def comparisonToScheme (F : etaleModules X) (i : ℕ) :=
  (modulesToSchemeLift (Y.p.obj y)).map (comparison f y U fU eU h_fst F i)

end AlgebraicGeometry.GroupoidsOver.HigherDirectImageComparison
