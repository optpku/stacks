module

public import stacks_project.Chap42.Lemma_42_49_3_AtZero
public import stacks_project.Chap42.Definition_42_46_3_DerivedChern
public import stacks_project.Chap42.Lemma_42_47_11_Pullback
public import stacks_project.Chap42.Lemma_42_47_11_IntersectionProduct
public import stacks_project.Chap42.Remark_42_34_7_Cutoff
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived

/-- A closed subscheme of an `S`-scheme locally of finite type is locally of finite
type over `S`. -/
instance closedOverSourceLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i] :
    LocallyOfFiniteType (Over.mk (i ≫ X.hom)).hom := sorry

/-- Complementary relative degrees in the Newton recurrence add to the successor degree. -/
theorem newtonClassAtZero_succ_degree (n j : ℕ) (hj : j ∈ Finset.range n) :
    ((j + 1 : ℕ) : ℤ) + ((n - j : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := sorry

/-- File-local additive structure on homogeneous bivariant classes. -/
-- Local instance justification (instance diamond): Lemma_42_35_4_Additive.instAddCommGroup cannot be imported with Lemma_42_35_3_Vanishing (duplicate zeroClass); a global pointwiseAddCommGroup instance diamonds with ChowCohomology.instAddCommGroupDegree.
local instance bivariantClassAddCommGroup
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) (p : ℤ) : AddCommGroup (BivariantClass δ f p) :=
  BivariantClass.pointwiseAddCommGroup δ f p

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z W T : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
variable [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
variable [IsClosedImmersion
  (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
    (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left]
variable (Q : RingedSpace.ModuleDerived W.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
variable (defined : ChernClass.Derived.IsDefined Q)
variable (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
variable [IsClosedImmersion t]
variable (containsComplement :
  (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
      (Set.range i.base)ᶜ ⊆ Set.range t.base)
variable (restrictionZero : IsZero
  ((RingedSpace.modulePullbackDerived
    (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
variable (classes : ChernClass.Theory δ X.hom)
variable (localizedNewton localizedChern :
  (p : ℕ) → BivariantClass δ
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
variable (localizedNewton_spec : ∀ p : ℕ, 0 < p →
  IsInfinityLocalizedExtension δ i b t (p : ℤ)
    (newtonClass δ (infinityCenter i b).hom
      (classes.reanchor (infinityCenter i b))
      ((RingedSpace.modulePullbackDerived
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
      (RingedSpace.modulePullbackDerived_isPerfect
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
        Q perfect)
      (IsDefined.pullback
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
        defined) p)
    (localizedNewton p))
variable (localizedChern_spec : ∀ p : ℕ, 0 < p →
  IsInfinityLocalizedExtension δ i b t (p : ℤ)
    (totalClass δ (infinityCenter i b).hom
      (classes.reanchor (infinityCenter i b))
      ((RingedSpace.modulePullbackDerived
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
      (RingedSpace.modulePullbackDerived_isPerfect
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
        Q perfect)
      (IsDefined.pullback
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
        defined) p)
    (localizedChern p))

include containsComplement restrictionZero localizedNewton_spec localizedChern_spec

/-- Lemma 42.49.6 (1): in the setup of Lemma 42.49.1, if `Q` restricts to zero on `T`,
then the Newton class at zero `P' 1 (Q)` equals the Chern class at zero `c' 1 (Q)` in
`A^* (Z ⟶ X)`. -/
@[stacks 0FAX]
theorem newtonClassAtZero_one :
    classAtZero δ i b 1 (localizedNewton 1) =
      classAtZero δ i b 1 (localizedChern 1) := sorry

/-- Lemma 42.49.6 (2): in the same restriction-zero setup, `P' 2 (Q)` equals
`c' 1 (Q) * c' 1 (Q) - 2 • c' 2 (Q)` in `A^* (Z ⟶ X)`, with relative multiplication
as in Remark 42.34.7. -/
@[stacks 0FAX]
theorem newtonClassAtZero_two :
    classAtZero δ i b 2 (localizedNewton 2) =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
          (classAtZero δ i b 1 (localizedChern 1))
          (classAtZero δ i b 1 (localizedChern 1)) -
        2 • classAtZero δ i b 2 (localizedChern 2) := sorry

/-- Lemma 42.49.6 (3): in the same restriction-zero setup,
`P' 3 (Q) = c' 1 (Q)^3 - 3 • (c' 1 (Q) * c' 2 (Q)) + 3 • c' 3 (Q)` in
`A^* (Z ⟶ X)`, with relative multiplication as in Remark 42.34.7. -/
@[stacks 0FAX]
theorem newtonClassAtZero_three :
    classAtZero δ i b 3 (localizedNewton 3) =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 1
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
            (classAtZero δ i b 1 (localizedChern 1))
            (classAtZero δ i b 1 (localizedChern 1)))
          (classAtZero δ i b 1 (localizedChern 1)) -
        3 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 2
          (classAtZero δ i b 1 (localizedChern 1))
          (classAtZero δ i b 2 (localizedChern 2)) +
        3 • classAtZero δ i b 3 (localizedChern 3) := sorry

/-- Lemma 42.49.6 (4): in the same restriction-zero setup, `P' 4 (Q)` is the usual
fourth Newton polynomial in the Chern classes at zero `c' i (Q)`, with relative
multiplication as in Remark 42.34.7. -/
@[stacks 0FAX]
theorem newtonClassAtZero_four :
    classAtZero δ i b 4 (localizedNewton 4) =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3 1
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 1
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
              (classAtZero δ i b 1 (localizedChern 1))
              (classAtZero δ i b 1 (localizedChern 1)))
            (classAtZero δ i b 1 (localizedChern 1)))
          (classAtZero δ i b 1 (localizedChern 1)) -
        4 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 2
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
            (classAtZero δ i b 1 (localizedChern 1))
            (classAtZero δ i b 1 (localizedChern 1)))
          (classAtZero δ i b 2 (localizedChern 2)) +
        4 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 3
          (classAtZero δ i b 1 (localizedChern 1))
          (classAtZero δ i b 3 (localizedChern 3)) +
        2 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 2
          (classAtZero δ i b 2 (localizedChern 2))
          (classAtZero δ i b 2 (localizedChern 2)) -
        4 • classAtZero δ i b 4 (localizedChern 4) := sorry

/-- Lemma 42.49.6 (5): in the same restriction-zero setup, the Newton classes at zero
satisfy the usual integral recurrence in the Chern classes at zero, with relative
multiplication as in Remark 42.34.7. -/
@[stacks 0FAX]
theorem newtonClassAtZero_succ (n : ℕ) :
    classAtZero δ i b ((n + 1 : ℕ) : ℤ) (localizedNewton (n + 1)) =
      (∑ j : Finset.range n,
        ((-1 : ℤ) ^ j.1) •
          BivariantClass.Nonnegative.castGrading δ
            (newtonClassAtZero_succ_degree n j.1 j.2)
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X)
              ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
              (classAtZero δ i b ((j.1 + 1 : ℕ) : ℤ) (localizedChern (j.1 + 1)))
              (classAtZero δ i b ((n - j.1 : ℕ) : ℤ) (localizedNewton (n - j.1))))) +
        (((-1 : ℤ) ^ n * (n + 1 : ℕ)) •
          classAtZero δ i b ((n + 1 : ℕ) : ℤ) (localizedChern (n + 1))) := sorry

end

end AlgebraicGeometry.LocalizedChern
