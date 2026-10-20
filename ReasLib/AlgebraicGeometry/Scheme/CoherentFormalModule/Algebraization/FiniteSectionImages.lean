module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.Affine
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.RingTheory.Topology.Adic.InverseLimit

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A Mittag-Leffler coherent formal module with adic limit topology and finite section images
canonically extends across the affine algebraization setup. -/
theorem canonicallyExtends_of_finiteSectionImages (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_mittagLeffler : IsMittagLeffler (sectionsSystem S F))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F))
    (h_finite : ∀ n : ℕ,
      Module.Finite A (LinearMap.range (limit.π (sectionsSystem S F) (op n)).hom)) :
    CanonicallyExtends S F := sorry

/-- If the base ring is adically complete, the same finite-section criterion places the coherent
formal module in the essential image of coherent completion. -/
theorem isCompletion_of_finiteSectionImages (S : AffineAlgebraizationSetup A)
    [IsAdicComplete S.I A]
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_mittagLeffler : IsMittagLeffler (sectionsSystem S F))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F))
    (h_finite : ∀ n : ℕ,
      Module.Finite A (LinearMap.range (limit.π (sectionsSystem S F) (op n)).hom)) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
