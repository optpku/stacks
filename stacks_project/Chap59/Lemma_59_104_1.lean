module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/- Lemma 59.104.1: if a morphism of schemes `f : X ⟶ Y` has a chosen section,
then the functor from Type-valued sheaves on `Y.smallEtaleTopology` to singleton
descent data along `f`, sending a sheaf to its canonical descent datum, is an
equivalence of categories. -/
@[stacks 0GEY] #check
  (AlgebraicGeometry.Scheme.EtaleSheaf.descentIsEquivalenceOfSection :
    {X Y : Scheme.{u}} → (f : X ⟶ Y) → SplitEpi f →
      (AlgebraicGeometry.Scheme.EtaleSheaf.pseudofunctor.toDescentData
        (fun _ : PUnit.{1} ↦ f)).IsEquivalence)

end AlgebraicGeometry.Scheme.EtaleSheaf
