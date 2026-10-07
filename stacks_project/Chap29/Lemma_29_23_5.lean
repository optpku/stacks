module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open
public import ReasLib.RingTheory.Ideal.GoingDown
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.MorphismProperty

universe u v

/- The affine going-down input turns openness of the map on prime spectra into going down. -/
#check
  (Algebra.HasGoingDown.of_isOpenMap :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S],
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) → Algebra.HasGoingDown R S)

/- Lemma 29.23.5 (1): an open morphism of schemes is generizing. -/
@[stacks 040F] #check
  (AlgebraicGeometry.generalizingMap_of_isOpenMap :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y}, IsOpenMap f.base → topologically GeneralizingMap f)

/- Lemma 29.23.5 (2): a universally open morphism of schemes is universally generizing. -/
@[stacks 040F] #check
  (@AlgebraicGeometry.universallyGeneralizing_of_universallyOpen :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [UniversallyOpen f],
      (topologically GeneralizingMap).universally f)
