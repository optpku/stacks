module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.RingTheory.UniqueFactorizationDomain.RegularLocal
public import ReasLib.RingTheory.CompleteIntersection.Local

@[expose] public section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- A complete-intersection local ring of Krull dimension at least four has a trivial Picard
group on its punctured spectrum. -/
instance subsingletonPicardGroup_of_completeIntersection
    {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
    [Fact ((4 : WithBot ℕ∞) ≤ ringKrullDim A)] :
    Subsingleton (AlgebraicGeometry.Scheme.PicardGroup (AlgebraicGeometry.PuncturedSpectrum.scheme A)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
