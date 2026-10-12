/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap67.Lemma_67_40_4
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap72.Definition_72_5_2_ResidueField
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup

/-!
# Proper pushforward of cycles on algebraic spaces

The proper pushforward of a cycle along a morphism of good algebraic spaces
weights fibres of `Points.map` by residue degree when relative dimension is
preserved, and otherwise by zero. This realises `f_*` on cycle groups of a
fixed relative dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Residue degree of a morphism of good algebraic spaces, using decency of the
source and target induced by the good structure morphisms. -/
noncomputable def residueDegreeAlong {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (h : X ⟶ Y) (x : Points X) : ℕ :=
  @residueDegree S X Y
    (@instIsDecent_of_isQuasiSeparated S X
      (IsQuasiSeparated.of_quasiSeparated pX))
    (@instIsDecent_of_isQuasiSeparated S Y
      (IsQuasiSeparated.of_quasiSeparated pY))
    h x

/-- Residue degree along a good morphism is the ordinary residue degree. -/
theorem residueDegreeAlong_eq {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (h : X ⟶ Y) (x : Points X) :
    residueDegreeAlong pX pY h x =
      @residueDegree S X Y
        (@instIsDecent_of_isQuasiSeparated S X
          (IsQuasiSeparated.of_quasiSeparated pX))
        (@instIsDecent_of_isQuasiSeparated S Y
          (IsQuasiSeparated.of_quasiSeparated pY))
        h x :=
  sorry

/-- Pushforward weight of a point: residue degree when `δ`-dimension is
preserved, and `0` otherwise. -/
noncomputable def mapCoeff {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (δ : Points B → ℤ) (f : X ⟶ Y) (x : Points X) : ℕ :=
  if (relativeDimensionFunction pX) δ x =
      (relativeDimensionFunction pY) δ (Points.map f x) then
    residueDegreeAlong pX pY f x
  else 0

/-- The pushforward weight is residue degree on dimension-preserving points and
zero otherwise. -/
theorem mapCoeff_eq {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (δ : Points B → ℤ) (f : X ⟶ Y) (x : Points X) :
    mapCoeff pX pY δ f x =
      if (relativeDimensionFunction pX) δ x =
          (relativeDimensionFunction pY) δ (Points.map f x) then
        residueDegreeAlong pX pY f x
      else 0 :=
  sorry

/-- Fibrewise residue-weighted sums along a proper morphism have locally finite
support. -/
theorem properPushforward_locallyFiniteSupport {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFiniteSupport fun y : Points Y ↦
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x :=
  sorry

/-- Proper pushforward of a cycle, summing residue-weighted fibres of
`Points.map f`. -/
def properPushforwardCycle {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points Y) ℤ where
  toFun y :=
    ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' y _ :=
    properPushforward_locallyFiniteSupport pX pY δ f hf α y

/-- Proper pushforward of cycles evaluates as the residue-weighted fibre sum. -/
theorem properPushforwardCycle_apply {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) (y : Points Y) :
    properPushforwardCycle pX pY δ f hf α y =
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x :=
  sorry

/-- Proper pushforward preserves relative degree `k`. -/
theorem properPushforward_mem_cycleGroup {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    {α : Function.locallyFinsupp (Points X) ℤ}
    (hα : α ∈ (cycleGroup pX) δ k) :
    properPushforwardCycle pX pY δ f hf α ∈ (cycleGroup pY) δ k :=
  sorry

/-- Proper pushforward as an additive map `Z_k(X) → Z_k(Y)`. -/
def properPushforwardHom {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ) :
    (cycleGroup pX) δ k →+ (cycleGroup pY) δ k where
  toFun α :=
    ⟨properPushforwardCycle pX pY δ f hf α,
      properPushforward_mem_cycleGroup pX pY δ f hf k α.property⟩
  map_zero' := sorry
  map_add' := sorry

/-- Structure morphisms of a composable pair over `B` remain compatible with the
composite. -/
theorem comp_structureMorphism_eq {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Y ⟶ Z} {pX : X ⟶ B} {pY : Y ⟶ B} {pZ : Z ⟶ B}
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY) :
    (f ≫ g) ≫ pZ = pX :=
  sorry

/-- Proper pushforward of raw locally finite cycles is functorial in the
morphism. -/
theorem properPushforwardCycle_comp {S : Scheme.{u}}
    {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (g : Y ⟶ Z) [Proper g]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    properPushforwardCycle pY pZ δ g hg
        (properPushforwardCycle pX pY δ f hf α) =
      properPushforwardCycle pX pZ δ (f ≫ g) (comp_structureMorphism_eq hf hg)
        α :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
