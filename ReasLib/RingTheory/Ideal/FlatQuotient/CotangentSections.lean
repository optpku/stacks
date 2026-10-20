module

public import ReasLib.RingTheory.Flat.Locus
public import ReasLib.RingTheory.Ideal.Cotangent.Sections
public import ReasLib.RingTheory.Ideal.FlatQuotient

@[expose] public section

open TopologicalSpace

universe u v

namespace Ideal.IsFlatQuotient

/-- For a local ring, quotient flatness along an ideal and flatness on a quasi-compact open
imply quotient flatness along the kernel of the ideal's cotangent map to sections on that open. -/
@[stacks 0ATC]
theorem cotangentSectionsKernel {A : Type u} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (U : TopologicalSpace.Opens (PrimeSpectrum A)) (M : Type v)
    [AddCommGroup M] [Module A M] (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (hI : I.IsFlatQuotient M)
    (hM : (U : Set (PrimeSpectrum A)) ⊆ Module.flatOverBaseLocus A A M) :
    (I.cotangentSectionsKernel U).IsFlatQuotient M := sorry

end Ideal.IsFlatQuotient
