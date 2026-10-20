module

import ReasLib.Topology.Sheaf.Cohomology.ClosedUnion
import StacksCheckRecall
@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

universe u

/- Exercise 111.60.5 (1) -/
@[stacks 0EEP] #check (TopCat.Sheaf.ClosedUnion.shortExact :
  ∀ {X : TopCat.{u}} {Y Z : Set X}, IsClosed Y → IsClosed Z →
    Y ∪ Z = Set.univ →
      (TopCat.Sheaf.ClosedUnion.shortComplex Y Z).ShortExact)

/- Exercise 111.60.5 (2): the Mayer–Vietoris sequence uses the explicit closed-embedding
cohomology isomorphisms and the additive Ext functor's biproduct isomorphism. -/
@[stacks 0EEP] #check (TopCat.Sheaf.ClosedUnion.integerCohomologySequence_exact :
  ∀ {X : TopCat.{u}} {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    [hX : HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [hYExt : HasExt.{u} ((TopCat.subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [hZExt : HasExt.{u} ((TopCat.subsetSpace Z).Sheaf AddCommGrpCat.{u})]
    [hWExt : HasExt.{u} ((TopCat.subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})]
    (n : ℕ),
      (TopCat.Sheaf.ClosedUnion.integerCohomologySequence hY hZ
        (TopCat.Sheaf.ClosedUnion.shortExact hY hZ hcover) n).Exact)

/- Exercise 111.60.5 (3) -/
@[stacks 0EEP] #check (TopCat.Sheaf.ClosedUnion.toSum_integerCohomology_zero_mono :
  ∀ {X : TopCat.{u}} {Y Z : Set X} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    [hX : HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    [hYExt : HasExt.{u} ((TopCat.subsetSpace Y).Sheaf AddCommGrpCat.{u})]
    [hZExt : HasExt.{u} ((TopCat.subsetSpace Z).Sheaf AddCommGrpCat.{u})]
    [hWExt : HasExt.{u} ((TopCat.subsetSpace (Y ∩ Z)).Sheaf AddCommGrpCat.{u})],
    Mono ((TopCat.Sheaf.ClosedUnion.integerCohomologySequence hY hZ
      (TopCat.Sheaf.ClosedUnion.shortExact hY hZ hcover) 0).map' 0 1))
