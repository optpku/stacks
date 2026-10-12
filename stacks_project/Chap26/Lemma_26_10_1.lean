/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion.Scheme
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Quasicoherent
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.10.1 (1): a closed subspace of a scheme has a compatible scheme presentation. -/
@[stacks 01IN] #check LocallyRingedSpace.IsClosedImmersion.Source.scheme
#check LocallyRingedSpace.IsClosedImmersion.Source.hom
#check LocallyRingedSpace.IsClosedImmersion.Source.hom_isClosedImmersion
#check LocallyRingedSpace.IsClosedImmersion.Source.iso
#check LocallyRingedSpace.IsClosedImmersion.Source.iso_hom_comp
#check LocallyRingedSpace.IsClosedImmersion.exists_schemeHom

/- Lemma 26.10.1 (2): the kernel ideal of a closed immersion into a scheme is quasi-coherent. -/
@[stacks 01IN] #check
  LocallyRingedSpace.Hom.KernelIdeal.isQuasicoherent

/- Lemma 26.10.1 (3): over any affine open, the closed immersion is the spectrum of the quotient
by its intrinsic affine-open kernel ideal. -/
#check LocallyRingedSpace.Hom.IsOpenRestriction
@[stacks 01IN] #check LocallyRingedSpace.Hom.AffineOpen.isIsomorphicQuotient
#check LocallyRingedSpace.Hom.AffineOpen.restrictedMap
#check LocallyRingedSpace.Hom.AffineOpen.globalSectionsKernelIdeal_eq

/- Lemma 26.10.1 (4): on an affine open the kernel ideal sheaf is the tilde sheaf of its
intrinsic affine-open kernel ideal. -/
@[stacks 01IN] #check LocallyRingedSpace.Hom.AffineOpen.kernelSheafIsomorphicTilde

/- The affine-chart restriction is an instance-producing bridge into the generic quotient API. -/
#check LocallyRingedSpace.Hom.kernelIdealOnOpen
#check LocallyRingedSpace.Hom.affineOpenKernelIdeal
#check LocallyRingedSpace.Hom.AffineChart.restrictedMap
#check LocallyRingedSpace.Hom.AffineChart.restrictedMap_isClosedImmersion
#check LocallyRingedSpace.Hom.AffineQuotient.comparison
#check LocallyRingedSpace.Hom.AffineQuotient.comparison_ι
#check LocallyRingedSpace.Hom.AffineQuotient.comparison_unique
#check LocallyRingedSpace.Hom.AffineQuotient.kernelSheafIsomorphicTilde

/- Generic restriction of a kernel ideal sheaf is reusable infrastructure for the affine
calculation, but is not a separate clause of Lemma 26.10.1. -/
#check LocallyRingedSpace.Hom.KernelIdealRestriction.iso
#check LocallyRingedSpace.Hom.KernelIdealRestriction.iso_preimage
#check LocallyRingedSpace.Hom.KernelIdealRestriction.iso_hom
#check LocallyRingedSpace.Hom.KernelIdealRestriction.iso_hom_kernelIdealι
#check LocallyRingedSpace.Hom.KernelIdealRestriction.mk_eq
#check LocallyRingedSpace.Hom.KernelIdealRestriction.mk_eq_preimage

/- Lemma 26.10.1, in particular: an ideal sheaf is locally generated exactly when it is
quasi-coherent. -/
@[stacks 01IN] #check
  Scheme.IdealSubobject.isLocallyGeneratedBySections_iff_isQuasicoherent
#check Scheme.Modules.IdealSubobject.isLocallyGeneratedBySections_iff_isQuasicoherent

end AlgebraicGeometry
