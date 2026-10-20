/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Specialization.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/- Lemma 62.4.5: if `R` is a discrete valuation ring with fraction field `K` and
residue field `κ`, and `f : X ⟶ Y` is a proper morphism of schemes locally of
finite type over `R`, then specialization of `r`-cycles commutes with proper
pushforward: `Y.hom.cycleSpecialization r ∘ mapHom (genericFiberMap f)` equals
`mapHom (specialFiberMap f) ∘ X.hom.cycleSpecialization r` on `Z_r`. -/
@[stacks 0H4M]
#check (AlgebraicGeometry.CycleGroup.cycleSpecialization_comp_mapHom :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (r : ℕ),
    (Y.hom.cycleSpecialization r).comp
      (mapHom (genericFiberMap f)
        (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
        (Y.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) =
      (mapHom (specialFiberMap f)
        (X.hom.fiberDimensionFunction (IsLocalRing.closedPoint R))
        (Y.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) r).comp
        (X.hom.cycleSpecialization r))

/- Specialization of an `r`-cycle on the generic fibre, then proper pushforward
on the special fibre, agrees with proper pushforward on the generic fibre
followed by specialization. -/
#check (AlgebraicGeometry.CycleGroup.cycleSpecialization_mapHom :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (r : ℕ)
    (α : CycleGroup X.hom.genericFiber
      (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
    Y.hom.cycleSpecialization r
      (mapHom (genericFiberMap f)
        (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
        (Y.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α) =
      mapHom (specialFiberMap f)
        (X.hom.fiberDimensionFunction (IsLocalRing.closedPoint R))
        (Y.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (X.hom.cycleSpecialization r α))

end AlgebraicGeometry.CycleGroup
