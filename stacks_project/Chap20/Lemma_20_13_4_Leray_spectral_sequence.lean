module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Leray
import StacksCheckRecall

@[expose] public section

/-!
# Leray spectral sequence

The canonical owner is the ringed-site specialization of the Grothendieck spectral sequence.
For a morphism of ringed spaces, specialize it along `opensRingedSiteHom`; no chapter-local
filtered complex or choice of comparison maps is needed.
-/

/- Lemma 20.13.4 (Leray spectral sequence): every bounded-below derived module admits a bounded,
convergent realization with second page `H^p(Y, R^q f_* K)` and abutment
`H^(p + q)(X, K)`. -/
@[stacks 01F2]
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.nonempty

#check @AlgebraicGeometry.RingedSpace.ModuleLeray.functorial
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.pageTwo_isIsomorphic_cohomology
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.abutment_isIsomorphic_hypercohomology

/- The page-two target and its textbook cohomology presentation are separate reusable views. -/
#check @RingedSite.Hom.Leray.pageTwo
#check @RingedSite.Hom.Leray.Ext.pageTwo
#check @RingedSite.Hom.Leray.Ext.pageTwo_isIsomorphic

/- The canonical abutment and its comparison with source global cohomology. -/
#check @RingedSite.Hom.Leray.abutment
#check @RingedSite.Hom.Leray.abutment_isIsomorphic

/- Realizations expose association, boundedness, finite filtrations, and convergence directly. -/
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.isAssociated
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.bounded
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.finite
#check @CategoryTheory.FilteredComplex.SpectralSequence.Realization.converges

/- Functoriality is part of the shared API rather than an implicit choice in the existence proof. -/
#check @RingedSite.Hom.Leray.functorial
#check @RingedSite.Hom.Leray.existsMap
#check @RingedSite.Hom.Leray.Map.id
#check @RingedSite.Hom.Leray.Map.comp

/- Ringed spaces enter the generic owner through their canonical opens ringed site. -/
#check @AlgebraicGeometry.RingedSpace.opensRingedSiteHom
