module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
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

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueDegreeAlong :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (pY : Y ⟶ B) [QuasiSeparated pY]
    (h : X ⟶ Y) (x : Points X),
    ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.mapCoeff :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) (f : X ⟶ Y) (x : Points X),
    ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.mapCoeff_eq :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX] (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) (f : X ⟶ Y) (x : Points X),
    mapCoeff pX pY δ f x =
      if (relativeDimensionFunction pX) δ x =
          (relativeDimensionFunction pY) δ (Points.map f x) then
        residueDegreeAlong pX pY f x
      else 0)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_locallyFiniteSupport :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ),
    LocallyFiniteSupport fun y : Points Y ↦
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ),
    Function.locallyFinsupp (Points Y) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle_apply :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α : Function.locallyFinsupp (Points X) ℤ) (y : Points Y),
    properPushforwardCycle pX pY δ f hf α y =
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_mem_cycleGroup :
  ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    {α : Function.locallyFinsupp (Points X) ℤ}
    (hα : α ∈ (cycleGroup pX) δ k),
    properPushforwardCycle pX pY δ f hf α ∈ (cycleGroup pY) δ k)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle_zero :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX),
    properPushforwardCycle pX pY δ f hf 0 = 0)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle_add :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (α β : Function.locallyFinsupp (Points X) ℤ),
    properPushforwardCycle pX pY δ f hf (α + β) =
      properPushforwardCycle pX pY δ f hf α +
        properPushforwardCycle pX pY δ f hf β)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardHom :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ),
    (cycleGroup pX) δ k →+ (cycleGroup pY) δ k)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardHom_apply :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (α : (cycleGroup pX) δ k),
    (properPushforwardHom pX pY δ f hf k α).val =
      properPushforwardCycle pX pY δ f hf α)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle_comp :
  ∀ {S : Scheme.{u}}
    {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (g : Y ⟶ Z) [Proper g]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY)
    (α : Function.locallyFinsupp (Points X) ℤ),
    properPushforwardCycle pY pZ δ g hg
        (properPushforwardCycle pX pY δ f hf α) =
      properPushforwardCycle pX pZ δ (f ≫ g) (by rw [Category.assoc, hg, hf])
        α)

end Hom

end AlgebraicGeometry.AlgebraicSpace
