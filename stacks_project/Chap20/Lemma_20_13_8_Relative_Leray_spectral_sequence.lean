module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.RelativeLeray
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.RelativeLeray
import StacksCheckRecall

@[expose] public section

/-!
# Relative Leray spectral sequence

The shared ringed-site owner packages the classical second page, the composite-pushforward
abutment, coherent maps, and the bounded-below derived extension.  Ringed spaces specialize it
through `opensRingedSiteHom`.
-/

/- Lemma 20.13.8 (Relative Leray spectral sequence): for composable morphisms, relative Leray
realizations can be chosen functorially in the module, with second page
`R^p g_* (R^q f_* F)` and abutment `R^(p + q) (f ≫ g)_* F`. -/
@[stacks 01F6]
#check @AlgebraicGeometry.RingedSpace.ModuleRelativeLeray.functorial

#check @AlgebraicGeometry.RingedSpace.ModuleRelativeLeray.pageTwo_isIsomorphic_higherDirectImage
#check @AlgebraicGeometry.RingedSpace.ModuleRelativeLeray.abutment_isIsomorphic_higherDirectImage

/- The objectwise realization, its targets, and maps are independently reusable. -/
#check @RingedSite.Hom.RelativeLeray.nonempty
#check @RingedSite.Hom.RelativeLeray.pageTwo
#check @RingedSite.Hom.RelativeLeray.abutment
#check @RingedSite.Hom.RelativeLeray.existsMap
#check @RingedSite.Hom.RelativeLeray.Map.id
#check @RingedSite.Hom.RelativeLeray.Map.comp

/- The same owner supplies the bounded-below derived-complex version from the source. -/
#check @RingedSite.Hom.RelativeLeray.BoundedBelow.nonempty
#check @RingedSite.Hom.RelativeLeray.BoundedBelow.pageTwo
#check @RingedSite.Hom.RelativeLeray.BoundedBelow.abutment
#check @RingedSite.Hom.RelativeLeray.BoundedBelow.functorial
#check @RingedSite.Hom.RelativeLeray.BoundedBelow.existsMap

#check @AlgebraicGeometry.RingedSpace.ModuleRelativeLeray.BoundedBelow.functorial
#check @AlgebraicGeometry.RingedSpace.ModuleRelativeLeray.BoundedBelow.pageTwo_isIsomorphic_higherDirectImage
#check @AlgebraicGeometry.RingedSpace.ModuleRelativeLeray.BoundedBelow.abutment_isIsomorphic_derivedPushforward

/- Association and convergence data are inherited from the neutral realization. -/
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.isAssociated
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.bounded
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.finite
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.converges

/- Ringed spaces enter the generic owner through their canonical opens ringed site. -/
#check @AlgebraicGeometry.RingedSpace.opensRingedSiteHom
