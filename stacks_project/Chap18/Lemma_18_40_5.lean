module

public import ReasLib.AlgebraicGeometry.RingedSite.LocallyRinged
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.5 (04H7) (1): inverse image along a morphism of sites preserves locally ringed
structure sheaves. -/
@[stacks 04H7 "(1)"]
#check @Sheaf.IsLocallyRinged.pullback

/- Lemma 18.40.5 (04H7) (2): an inverse-image equivalence and a structure-sheaf isomorphism
preserve and reflect locally ringedness. -/
@[stacks 04H7 "(2)"]
#check @Sheaf.isLocallyRinged_iff_of_pullback_equivalence

#check @Sheaf.isLocallyRinged_iff_of_iso
#check @RingedSite.Hom.isLocallyRinged_iff_of_equivalence
