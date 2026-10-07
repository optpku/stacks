module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.8 (04H9) (1): a local bundled morphism induces local maps on stalk rings. -/
@[stacks 04H9 "(1)"]
#check @RingedSite.Hom.stalkMap_isLocalHom

/- Lemma 18.40.8 (04H9) (2): enough points detect locality through the canonical stalk maps. -/
@[stacks 04H9 "(2)"]
#check @RingedSite.Hom.isLocal_iff_stalkMap_isLocalHom

/- Lemma 18.40.8 (04H9) (3): local maps between local stalk rings are characterized by the
maximal-ideal pullback equality. -/
@[stacks 04H9 "(3)"]
#check @RingedSite.Hom.stalkMap_isLocalHom_iff_comap_maximalIdeal

/- Lemma 18.40.8 (04H9) (4): a conservative family of local stalk maps detects global locality. -/
@[stacks 04H9 "(4)"]
#check @RingedSite.Hom.IsLocal.of_stalkMap

/- Lemma 18.40.8 (04H9) (5): the conservative-family criterion specializes to locally ringed
presentations; the ReasLib theorem is stated at the stronger ambient ringed-site level. -/
@[stacks 04H9 "(5)"]
#check @RingedSite.Hom.IsLocal.of_stalkMap
