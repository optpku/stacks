module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Dimension
import StacksCheckRecall

/-! # Lemma 69.10.1: Vanishing above the dimension -/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyWithSupport`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.10.1: Vanishing above an integer dimension bound. -/
@[stacks 0A4R] #check (AlgebraicGeometry.AlgebraicSpace.cohomology_isZero_of_dimension_le :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (d : ℤ) (hdim : dimensionLEInt X d) (F : X.Modules) [F.IsQuasicoherent]
    {q : ℤ} (hq : d < q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsZero (cohomologyInt X F q))

/- Lemma 69.10.1: Surjectivity of top-degree restriction. -/
@[stacks 0A4R] #check (AlgebraicGeometry.AlgebraicSpace.cohomologyRestrict_surjective_of_dimension_le :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S}
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
    [PreservesFiniteColimits (etaleRestrictionSheaf ι AddCommGrpCat.{u})],
    Epi (cohomologyRestrictInt ι F d))

/- Lemma 69.10.1: Vanishing with closed support and quasi-compact complement. -/
@[stacks 0A4R] #check (AlgebraicGeometry.AlgebraicSpace.cohomologyWithSupport_isZero_of_dimension_le :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
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
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsZero (cohomologyWithSupportInt i F q))
