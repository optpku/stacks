module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 85.2.1: let `X` be a simplicial space. Then `X_Zar` as defined above is a site. -/
@[stacks 09VL] #check (CategoryTheory.SimplicialObject.instZariskiCoveringsIsSite :
  ∀ (X : CategoryTheory.SimplicialObject TopCat.{u}),
    CategoryTheory.PreZeroHypercover.IsSite
      (CategoryTheory.SimplicialObject.zariskiCoverings X))
