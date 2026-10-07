module

public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Pointed
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

universe u

/- Remark 17.6.4 (1): pushforward of pointed sheaves along the inclusion of a closed subset is
exact. -/
@[stacks 01B0 "(1)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.pushforwardExact hZ :
    exactFunctor ((TopCat.of Z).Sheaf Pointed.{u}) (X.Sheaf Pointed.{u})
      (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)))

/- Remark 17.6.4 (2): pointed sections supported on a closed subset form a functor to pointed
sheaves on that subset. -/
@[stacks 01B0 "(2)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.functor hZ :
    X.Sheaf Pointed.{u} ⥤ (TopCat.of Z).Sheaf Pointed.{u})

/- The kernel description identifies its local sections with sections restricting to the
distinguished point on the open complement. -/
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (F : X.Sheaf Pointed.{u}) (U : Opens X) (s : F.presheaf.obj (Opposite.op U)) ↦
  TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.mem_range_inclusion_app_iff
    hZ F U s

/- Remark 17.6.4 (3): the pointed sections-with-support functor is right adjoint to closed-subset
pushforward. -/
@[stacks 01B0 "(3)"]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.adjunction hZ :
    Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z) ⊣
      TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.functor hZ)
