module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.GroupTheory.FreeAbelianGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import stacks_project.Chap62.Example_62_5_4_AssociatedCycle
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Definition_62_6_1_Specialization

/-!
# Cycle classes of Hilbert points

This file packages the set `Hilb(X/S, r)` of closed subschemes flat of relative
dimension at most `r`, and the homomorphism from the free abelian group on that
set to `z(X/S, r)` sending a generator to `[Z/X/S]_r`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The set `Hilb(X/S, r)` of closed subschemes `Z ⊂ X` such that `Z ⟶ S` is
flat and of relative dimension at most `r`. -/
structure Hilb {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) where
  /-- The ideal sheaf of the closed subscheme `Z ⊂ X`. -/
  ideal : X.IdealSheafData
  /-- The structure morphism `Z ⟶ S` is flat. -/
  flat : Flat (ideal.subschemeι ≫ f)
  /-- The structure morphism `Z ⟶ S` has relative dimension at most `r`. -/
  relativeDimensionLE : Scheme.Hom.RelativeDimensionLE (ideal.subschemeι ≫ f) r

namespace Hilb

/-- Construct a point of `Hilb(X/S, r)` from a closed subscheme that is flat of
relative dimension at most `r` over `S`. -/
def ofIdeal {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) (ideal : X.IdealSheafData)
    (flat : Flat (ideal.subschemeι ≫ f))
    (relativeDimensionLE : Scheme.Hom.RelativeDimensionLE (ideal.subschemeι ≫ f) r) :
    Hilb f r where
  ideal := ideal
  flat := flat
  relativeDimensionLE := relativeDimensionLE

/-- The structure morphism `Z ⟶ S` of a point of `Hilb(X/S, r)`. -/
def structureMap {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (Z : Hilb f r) :
    Z.ideal.subscheme ⟶ S :=
  Z.ideal.subschemeι ≫ f

/-- The structure morphism is the closed immersion of `Z` followed by `f`. -/
theorem structureMap_def {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (Z : Hilb f r) :
    Z.structureMap = Z.ideal.subschemeι ≫ f := sorry

/-- The structure morphism of a Hilbert point is flat. -/
theorem flat_structureMap {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (Z : Hilb f r) :
    Flat Z.structureMap := sorry

/-- The structure morphism of a Hilbert point has relative dimension at most `r`. -/
theorem relativeDimensionLE_structureMap {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (Z : Hilb f r) : Scheme.Hom.RelativeDimensionLE Z.structureMap r := sorry

/-- A point of `Hilb(X/S, r)` is a closed subscheme whose structure morphism is
flat of relative dimension at most `r`. -/
theorem spec {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (Z : Hilb f r) :
    IsClosedImmersion Z.ideal.subschemeι ∧
      Flat Z.structureMap ∧
      Scheme.Hom.RelativeDimensionLE Z.structureMap r := sorry

end Hilb

/-- Unbundled recognition of a closed subscheme of `X` as an element of
`Hilb(X/S, r)`. -/
def IsHilb {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) (Z : X.IdealSheafData) : Prop :=
  Flat (Z.subschemeι ≫ f) ∧ Scheme.Hom.RelativeDimensionLE (Z.subschemeι ≫ f) r

/-- A closed subscheme arises from `Hilb(X/S, r)` if and only if `Z ⟶ S` is
flat of relative dimension at most `r`. -/
theorem isHilb_iff {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) (Z : X.IdealSheafData) :
    (∃ Z' : Hilb f r, Z'.ideal = Z) ↔ IsHilb f r Z := sorry

/-- A relative-dimension bound on `Z ⟶ S` yields the fibrewise topological
dimension bound `dim(Z_s) ≤ r` needed to form `[Z/X/S]_r`. -/
theorem fiberClosedSubschemeDimensionLE_of_relativeDimensionLE
    {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (Z : Hilb f r) :
    f.fiberClosedSubschemeDimensionLE Z.ideal r := sorry

/-- The relative `r`-cycle `[Z/X/S]_r` associated to a point of `Hilb(X/S, r)`. -/
noncomputable def cycleClass {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (Z : Hilb f r) : Family f r :=
  f.closedSubschemeFiberCycleFamily Z.ideal r
    (fiberClosedSubschemeDimensionLE_of_relativeDimensionLE Z)

/-- The generator value `[Z/X/S]_r` is the associated fibrewise cycle family of
the underlying closed subscheme. -/
theorem cycleClass_eq {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (Z : Hilb f r) :
    cycleClass f r Z =
      f.closedSubschemeFiberCycleFamily Z.ideal r
        (fiberClosedSubschemeDimensionLE_of_relativeDimensionLE Z) := sorry

/-- The generator `[Z/X/S]_r` is a relative `r`-cycle on `X / S`. -/
theorem cycleClass_isRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (Z : Hilb f r) :
    IsRelative (cycleClass f r Z) := sorry

/-- The homomorphism from the free abelian group on `Hilb(X/S, r)` to families of
fibrewise `r`-cycles, sending `∑ n_i [Z_i]` to `∑ n_i [Z_i/X/S]_r`. -/
noncomputable def cycleClassHom {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) :
    FreeAbelianGroup (Hilb f r) →+ Family f r :=
  FreeAbelianGroup.lift (cycleClass f r)

/-- The cycle-class homomorphism sends a generator `[Z]` to `[Z/X/S]_r`. -/
theorem cycleClassHom_of {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (Z : Hilb f r) :
    cycleClassHom f r (FreeAbelianGroup.of Z) = cycleClass f r Z := sorry

/-- The image of the cycle-class homomorphism consists of relative `r`-cycles. -/
theorem cycleClassHom_isRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (σ : FreeAbelianGroup (Hilb f r)) :
    IsRelative (cycleClassHom f r σ) := sorry

/-- The cycle-class homomorphism lands in the group `z(X/S, r)` of relative
`r`-cycles. -/
theorem cycleClassHom_mem_group {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (σ : FreeAbelianGroup (Hilb f r)) :
    cycleClassHom f r σ ∈ group f r := sorry

/-- The source-facing homomorphism from the free abelian group on `Hilb(X/S, r)`
to `z(X/S, r)`, obtained by restricting the codomain of `cycleClassHom`. -/
noncomputable def cycleClassHomToGroup {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    FreeAbelianGroup (Hilb f r) →+ group f r :=
  (cycleClassHom f r).codRestrict (group f r) (cycleClassHom_mem_group f r)

/-- The underlying fibrewise family of `cycleClassHomToGroup` is `cycleClassHom`. -/
@[simp]
theorem coe_cycleClassHomToGroup {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (σ : FreeAbelianGroup (Hilb f r)) :
    (cycleClassHomToGroup f r σ : Family f r) = cycleClassHom f r σ := sorry

end AlgebraicGeometry.RelativeCycle
