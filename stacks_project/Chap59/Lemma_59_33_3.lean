module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Henselization
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 59.33.3: the henselization of the stalk at s is the filtered colimit
   of sections over elementary etale neighborhoods of (S, s). -/
@[stacks 04HY] #check (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.nonempty_henselizationIsoColimit :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (s : S) (Rh : Type u),
    [CommRing Rh] → [Algebra (S.presheaf.stalk s) Rh] →
      [IsHenselizationOf (S.presheaf.stalk s) Rh] →
        Nonempty ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of Rh) ≅
          colimit (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.sections S s)))
