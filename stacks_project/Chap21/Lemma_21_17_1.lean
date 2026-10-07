module

public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Homotopy.BifunctorTotal

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable (G : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)

/- Lemma 21.17.1 (06YM) (1): fixing `G` on the left gives an exact tensor-totalization
endofunctor of the homotopy category of `O`-module complexes. -/
@[stacks 06YM "(1)"]
#check (inferInstance :
  (leftFixed (curriedTensor (ringedSiteModuleCategory.{u, v, w, w} J O)) G).IsTriangulated)

/- Lemma 21.17.1 (06YM) (2): fixing `G` on the right gives an exact tensor-totalization
endofunctor of the homotopy category of `O`-module complexes. -/
@[stacks 06YM "(2)"]
#check (inferInstance :
  (rightFixed (curriedTensor (ringedSiteModuleCategory.{u, v, w, w} J O)) G).IsTriangulated)

end SheafOfModules.RingedSite
