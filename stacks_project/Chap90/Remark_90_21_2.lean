module

public import stacks_project.Chap90.Remark_90_21_2_Comparison
import StacksCheckRecall

/-!
# Groupoids in functors versus functors to groupoids

A groupoid in functors on `C` amounts to a functor `C ⥤ Grpd`, and a morphism of
groupoids in functors amounts to a morphism of those functors, where `Grpd` is
regarded as a 1-category. The preferred owner remains `GroupoidInFunctors`:
identifying a groupoid in functors with the corresponding functor, or with the
associated cofibered category `Functor.ofGroupoidValued G.toFunctor`, can lead to
confusion (Remark 90.23.2).
-/

@[expose] public section

open CategoryTheory

universe u v w

/- Remark 90.21.2 (1): a groupoid in functors on `C` amounts to the data of a
functor `C ⥤ Grpd`, where `Grpd` is regarded as a 1-category. -/
@[stacks 06K4] #check GroupoidInFunctors.toFunctor

/- Remark 90.21.2 (2): a morphism of groupoids in functors on `C` amounts to a
morphism of the corresponding functors `C ⥤ Grpd`. -/
@[stacks 06K4] #check GroupoidInFunctors.Hom.equivToNatTrans
