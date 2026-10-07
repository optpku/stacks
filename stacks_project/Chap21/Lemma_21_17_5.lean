module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

namespace SheafOfModules.RingedSite

open CategoryTheory

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})

/- Lemma 21.17.5 (07A2): the totalized tensor product of two K-flat cochain complexes of
`O`-modules on the ringed site `(C, J, O)` is K-flat. -/
@[stacks 07A2]
#check CochainComplex.IsKFlat.tensor
  (C := ringedSiteModuleCategory.{u, v, w, w} J O)

end

end SheafOfModules.RingedSite
