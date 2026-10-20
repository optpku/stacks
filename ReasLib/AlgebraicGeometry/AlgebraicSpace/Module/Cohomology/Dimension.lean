module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.IntegerBound
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent

/-! # Dimension bounds for quasi-coherent étale cohomology of algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyWithSupport`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale cohomology of a quasi-coherent module on a quasi-compact
quasi-separated algebraic space vanishes in degrees strictly larger than `dim X`. -/
@[stacks 0A4R]
theorem cohomology_isZero_of_dimension_le
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℤ) (hdim : dimensionLEInt X d) (F : X.Modules) [F.IsQuasicoherent]
    {q : ℤ} (hq : d < q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomologyInt X F q) :=
  sorry

/-- In the top degree allowed by `dim X`, restriction of étale
cohomology of a quasi-coherent module to a quasi-compact open subspace is surjective. -/
@[stacks 0A4R]
theorem cohomologyRestrict_surjective_of_dimension_le
    {S : Scheme.{u}} {X U : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℤ) (hdim : dimensionLEInt X d)
    (ι : U ⟶ X) [IsOpenImmersion ι] [IsQuasiCompact U]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf ι AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})]
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})] :
    Epi (cohomologyRestrictInt ι F d) :=
  sorry

/-- Étale cohomology with support in a closed subspace whose complement
is quasi-compact vanishes in degrees strictly larger than `dim X`. -/
@[stacks 0A4R]
theorem cohomologyWithSupport_isZero_of_dimension_le
    {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℤ) (hdim : dimensionLEInt X d)
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsQuasiCompact (closedImmersionComplement i)]
    (F : X.Modules) [F.IsQuasicoherent]
    {q : ℤ} (hq : d < q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleTopology (closedImmersionComplement i)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (smallEtaleTopology (closedImmersionComplement i)) AddCommGrpCat.{u})]
    [(etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits
      (etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u})]
    [PreservesFiniteColimits
      (etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero (cohomologyWithSupportInt i F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
