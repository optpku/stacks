module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Free
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.6

The reusable owner separates graded-flatness from relative K-flatness and then combines them into
fixed-base goodness.  The source's stronger assertion that the free module remains good after
arbitrary ringed-topos pullback belongs to the geometric universal-goodness layer.
-/

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J (Type w)]
variable {O : Sheaf J CommRingCat.{w}}
variable (A : DGA(O)) (S : IntGradedSheaf.{u, v, w} J)

/- Lemma 24.23.6 (0FSG), fixed-base component: `A[S]` is good over the current ringed site and
differential graded algebra. -/
@[stacks 0FSG "fixed-base free DG modules are good"]
#check
  (IsGoodAtBase.freeOnGradedSheaf A S :
    IsGoodAtBase ((DifferentialGradedModule.freeOnGradedSheaf A).obj S))

/- Fine-grained fixed-base components, usable independently downstream. -/
#check
  (IsGradedFlat.freeOnGradedSheaf A S :
    IsGradedFlat ((DifferentialGradedModule.freeOnGradedSheaf A).obj S))
#check
  (IsKFlat.freeOnGradedSheaf A S :
    IsKFlat ((DifferentialGradedModule.freeOnGradedSheaf A).obj S))

/- Generic preservation statements for the free-DG-module functor on a coefficient complex. -/
variable (K : CochainComplex
  (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O)) ℤ)

#check
  (IsGradedFlat.freeFunctor A K :
    HomologicalComplex.IsTermwiseFlat K →
      IsGradedFlat ((DifferentialGradedModule.freeFunctor A).obj K))
#check
  (IsKFlat.freeFunctor A K :
    HomologicalComplex.IsKFlat K →
      IsKFlat ((DifferentialGradedModule.freeFunctor A).obj K))
#check
  (IsGoodAtBase.freeFunctor A K :
    HomologicalComplex.IsTermwiseFlat K → HomologicalComplex.IsKFlat K →
      IsGoodAtBase ((DifferentialGradedModule.freeFunctor A).obj K))

end SheafOfModules.RingedSite.DifferentialGradedModule

end
