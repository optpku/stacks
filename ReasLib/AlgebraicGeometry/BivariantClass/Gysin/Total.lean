/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.RegularImmersion
public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Closed
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

variable {k : Type u} [Field k]

/-- The integral Gysin action of a regular immersion on total Chow homology, assembled
from its normal Gysin coefficients on clopen rank loci. The degree bound uses the
vanishing of negative Chow groups over a field. -/
noncomputable def gysinMapOfRankLoci
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : Y ⟶ X) [IsRegularImmersion i.left]
    (Di : Gysin.NormalSpecializationOfRankLoci i) :
    ChowGroup.Total (fun _ ↦ 0) X →+ ChowGroup.Total (fun _ ↦ 0) Y :=
  DirectSum.toAddMonoid fun n ↦
    ∑ c ∈ Finset.range (n.toNat + 1),
      (DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) Y d) (n - c)).comp
        ((gysinSectionOfRankLoci (fun _ ↦ 0) i Di c).cap
          (𝟙 Y) i (𝟙 X) IsPullback.of_id_fst n)

/-- On a homogeneous class, the total Gysin action is the finite sum of its normal
Gysin caps in degrees `n - c`. -/
theorem gysinMapOfRankLoci_of
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : Y ⟶ X) [IsRegularImmersion i.left]
    (Di : Gysin.NormalSpecializationOfRankLoci i) {n : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) X n) :
    gysinMapOfRankLoci i Di (DirectSum.of _ n alpha) =
      ∑ c ∈ Finset.range (n.toNat + 1),
        DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) Y d) (n - c)
          ((gysinSectionOfRankLoci (fun _ ↦ 0) i Di c).cap
            (𝟙 Y) i (𝟙 X) IsPullback.of_id_fst n alpha) := sorry

/-- The total Gysin action is independent of the model of deformation to the normal cone. -/
theorem gysinMapOfRankLoci_independent
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : Y ⟶ X) [IsRegularImmersion i.left]
    (Di Di' : Gysin.NormalSpecializationOfRankLoci i) :
    gysinMapOfRankLoci i Di = gysinMapOfRankLoci i Di' := sorry

end AlgebraicGeometry.BivariantClass
