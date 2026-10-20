module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
public import ReasLib.RingTheory.Localization.FractionRing.Separable
public import ReasLib.RingTheory.RingHom.IndSmooth.Factorization
import ReasLib.RingTheory.Smooth.NeronBlowup.Termination

/-!
# Ind-smooth weakly unramified extensions of DVRs

Neron desingularization supplies smooth factorizations of all finitely
presented test algebras.  The generic factorization criterion then identifies
the extension map as a filtered colimit of smooth maps.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace IsExtensionOfDiscreteValuationRings.WeaklyUnramified

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L] [IsExtensionOfDiscreteValuationRings R L]
variable [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]

/-- Smooth factorization of every finite-presentation test map into a weakly unramified DVR
extension with separable residue- and fraction-field extensions. -/
@[stacks 0BJ7]
theorem hasFactorisations
    [Algebra.IsSeparableOver (ResidueField R) (ResidueField L)]
    [FractionRing.IsSeparableExtension R L] :
    RingHom.IndSmooth.HasFactorisations (algebraMap R L) := sorry

/-- Lemma 16.4.6 (tag 0BJ7): a weakly unramified extension of discrete valuation rings with
separable residue- and fraction-field extensions is a filtered colimit of smooth algebras. -/
@[stacks 0BJ7]
theorem indSmooth
    [Algebra.IsSeparableOver (ResidueField R) (ResidueField L)]
    [FractionRing.IsSeparableExtension R L] :
    (algebraMap R L).IndSmooth := sorry

end IsExtensionOfDiscreteValuationRings.WeaklyUnramified
