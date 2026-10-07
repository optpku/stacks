module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Augmentation
import StacksCheckRecall

@[expose] public section

/- Lemma 20.10.4 (Tag 01EM): for an indexed open cover `𝒰` of `U` (with `iSup 𝒰 = U`), the
homology of the free Čech chain is the image of its degree-zero augmentation in degree `0` and
vanishes in every nonzero degree.  The geometric owner keeps the cover equation explicit. -/

open AlgebraicGeometry.RingedSpace.ModuleCech
open SheafOfModules.RingedSite.Cech

@[stacks 01EM] #check @chain
@[stacks 01EM] #check @AlgebraicGeometry.RingedSpace.ModuleCech.augmentation
@[stacks 01EM] #check @SheafOfModules.RingedSite.Cech.augmentation_comp_ι
@[stacks 01EM] #check @homology_zero_isomorphic_image
@[stacks 01EM] #check @homology_isZero_of_ne_zero
@[stacks 01EM] #check @homology_succ_isZero

end
