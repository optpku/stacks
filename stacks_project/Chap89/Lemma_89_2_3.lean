module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap72.Definition_72_8_1_Modification
public import stacks_project.Chap72.Definition_72_8_3_Alteration
public import stacks_project.Chap89.«89_2_0_1_Punctured»

/-!
# Dimension of the special fibre of a modification

If `(A, 𝔪, κ)` is a Noetherian local domain of dimension at least `1` and
`f : X ⟶ specSpace A` is a morphism of algebraic spaces satisfying one of
the listed conditions, then
`dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The unique generic point of `specSpace A`, as the image of the generic
point of `Spec (.of A)` under `ofOver.pointsEquiv`. -/
noncomputable def specSpaceGenericPoint (A : Type u) [CommRing A] [IsDomain A] :
    Points (specSpace A) :=
  ofOver.pointsEquiv (Over.mk (𝟙 (Spec (.of A)))) (genericPoint (Spec (.of A)))

/-- `specSpaceGenericPoint A` is `ofOver.pointsEquiv` of the generic point of
`Spec (.of A)`. -/
theorem specSpaceGenericPoint_eq (A : Type u) [CommRing A] [IsDomain A] :
    specSpaceGenericPoint A =
      ofOver.pointsEquiv (Over.mk (𝟙 (Spec (.of A))))
        (genericPoint (Spec (.of A))) :=
  sorry

/-- Lemma 89.2.3 (1) Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is a modification of algebraic spaces,
then `dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
@[stacks 0AYJ]
theorem dimension_specialFiber_le_of_isModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] [IsIntegral (specSpace A)] (f : X ⟶ specSpace A)
    [IsModification f] :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

/-- Lemma 89.2.3 (2) Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is an alteration of algebraic spaces,
then `dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
@[stacks 0AYJ]
theorem dimension_specialFiber_le_of_isAlteration
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] [IsIntegral (specSpace A)] (f : X ⟶ specSpace A)
    [IsAlteration f] :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

/-- Lemma 89.2.3 (3) Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is locally of finite type and
quasi-separated, `X` is integral, and there is exactly one point of `Points X`
mapping to the generic point of `specSpace A`, then
`dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
@[stacks 0AYJ]
theorem dimension_specialFiber_le_of_unique_genericPoint_preimage
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A) [LocallyOfFiniteType f]
    [QuasiSeparated f]
    (hη : ∃! x : Points X, Points.map f x = specSpaceGenericPoint A) :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

/-- Lemma 89.2.3 (4) Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is locally of finite type, `X` is
decent, and the points of `Points X` mapping to the generic point of
`specSpace A` are the generic points of irreducible components of `Points X`,
then `dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
@[stacks 0AYJ]
theorem dimension_specialFiber_le_of_genericPoint_preimage_eq_genericPoints
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsDecent X] (f : X ⟶ specSpace A) [LocallyOfFiniteType f]
    (hη : Points.map f ⁻¹' {specSpaceGenericPoint A} = genericPoints X) :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
