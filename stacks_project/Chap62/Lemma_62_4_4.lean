module

public import ReasLib.AlgebraicGeometry.CycleGroup.Specialization.FlatPullback
import StacksCheckRecall

/-!
# Lemma 62.4.4

Specialization of cycles over a discrete valuation ring commutes with flat
pullback along a morphism of relative dimension `e`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/- Lemma 62.4.4: if `R` is a discrete valuation ring with fraction field `K`
and residue field `κ`, `X` is locally of finite type over `R`, and
`f : X' ⟶ X` is locally of finite type, flat, and of relative dimension `e`,
then specialization of cycles over `R` commutes with flat pullback:
`(X'.hom.cycleSpecialization (r + e)).comp (genericFiberFlatPullback f e r)`
equals `(specialFiberFlatPullback f e r).comp (X.hom.cycleSpecialization r)`
as maps `Z_r(X_K) → Z_{r+e}(X'_κ)`. -/
@[stacks 0H4L] #check (AlgebraicGeometry.CycleGroup.cycleSpecialization_comp_flatPullback :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ),
    (X'.hom.cycleSpecialization (r + e)).comp (genericFiberFlatPullback f e r) =
      (specialFiberFlatPullback f e r).comp (X.hom.cycleSpecialization r))

/- Specialization of an `r`-cycle on the generic fibre, then flat pullback on
the special fibre, agrees with flat pullback on the generic fibre followed by
specialization. -/
#check (AlgebraicGeometry.CycleGroup.cycleSpecialization_flatPullback :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ)
    (α : CycleGroup X.hom.genericFiber
      (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
    X'.hom.cycleSpecialization (r + e) (genericFiberFlatPullback f e r α) =
      specialFiberFlatPullback f e r (X.hom.cycleSpecialization r α))

end AlgebraicGeometry.CycleGroup
