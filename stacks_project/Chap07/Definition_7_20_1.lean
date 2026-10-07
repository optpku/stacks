module

public import stacks_project.Chap07.Definition_7_20_1_Cocontinuous
import StacksCheckRecall

@[expose] public section

/- Definition 7.20.1: a functor u : C ⥤ D of sites is cocontinuous when every
covering {Vⱼ ⟶ u(U)} of D admits a covering {Uᵢ ⟶ U} of C whose image family
{u(Uᵢ) ⟶ u(U)} refines it. The image family need not itself be a covering of D.
This is the selected-cover owner Functor.Precoverage.IsCocontinuous. -/
@[stacks 00XJ] #check @CategoryTheory.Functor.Precoverage.IsCocontinuous
