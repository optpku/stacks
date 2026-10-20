module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Henselization
public import ReasLib.RingTheory.Henselian.Henselization
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Henselization
import StacksCheckRecall

/-!
# Henselian local rings of decent algebraic spaces along elementary neighbourhoods

The henselian local ring of a decent algebraic space at a point identifies with the
henselization of the Zariski local ring of any elementary étale neighbourhood.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicSpace EtaleNeighborhood
open CategoryTheory CategoryTheory.Limits

/- Lemma 68.11.8: The henselian local ring of a decent algebraic space at a point
is the henselization of the local ring of any elementary étale neighbourhood. -/
@[stacks 0EMY] #check
  (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.nonempty_iso_henselization :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
      (U : Elementary X x) (Rh : Type u) [CommRing Rh]
      [Algebra ((scheme U.obj).presheaf.stalk (point U.obj)) Rh]
      [IsHenselizationOf ((scheme U.obj).presheaf.stalk (point U.obj)) Rh],
      Nonempty
        ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of Rh) ≅
          henselianLocalRingCat X x))
