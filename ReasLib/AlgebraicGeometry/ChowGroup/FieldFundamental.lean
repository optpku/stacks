module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cartesian
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The degree-zero fundamental Chow class of the spectrum of a field. -/
noncomputable def specFundamentalClass (k : Type u) [Field k] :
    RelativeChow (fun _ ↦ 0) (⊤_ (SchemeOverField k)) 0 :=
  @chowClass (⊤_ (SchemeOverField k)).left
    (@LocallyOfFiniteType.isLocallyNoetherian _ _ (⊤_ (SchemeOverField k)).hom
      inferInstance (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
        (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
    ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance 0
    (@CycleGroup.fundamental (⊤_ (SchemeOverField k)).left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (⊤_ (SchemeOverField k)).hom
        inferInstance (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0)) 0)

/-- The fundamental class of a field spectrum is represented by its fundamental cycle. -/
theorem specFundamentalClass_def (k : Type u) [Field k] :
    specFundamentalClass k =
      @chowClass (⊤_ (SchemeOverField k)).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (⊤_ (SchemeOverField k)).hom
          inferInstance (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance 0
        (@CycleGroup.fundamental (⊤_ (SchemeOverField k)).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (⊤_ (SchemeOverField k)).hom
            inferInstance (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0)) 0) := sorry

end AlgebraicGeometry.ChowGroup
