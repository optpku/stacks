module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange.BoundedBelow
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.15.1

The reusable owner is the bounded-below natural transformation in
`RingedSite.Hom.DerivedBaseChange.BoundedBelow`.  Its source and target are `Rf_* ⋙ g^*` and
`(g')^* ⋙ R(f')_*`; flatness supplies the two exact horizontal functors.  The library keeps the
module pullback square explicit, while `mapOfCommSq` supplies the strict-square specialization.
-/

/- Lemma 21.15.1 (0736): a commutative square of ringed topoi with flat horizontal morphisms
has a canonical bounded-below base-change transformation
`g^* Rf_* ⟶ R(f')_* (g')^*`. -/
@[stacks 0736]
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.map

#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.app
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.mapOfCommSq
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.sourceComparison_isIso
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.IsMap
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.IsMap.eq_map
