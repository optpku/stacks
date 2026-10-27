/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.GradedRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleFiniteLocallyFree

/-! # Operational first Chern classes of invertible modules -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L]

/-- The first Chern cap family of the pulled-back invertible module. -/
def family : OperationalChow.CapFamily δ f 1 :=
  fun {Y} g _ _ k ↦
    @FirstChernChow.lower S B Y _ _ (g ≫ f) _ _ δ _
      ((Modules.pullback g).obj L) (Modules.isInvertibleObject_pullback g L) k

/-- The first Chern cap family commutes with proper pushforward. -/
theorem proper : OperationalChow.CompatibleWithProperPushforward δ f (family f δ L) := sorry

/-- The first Chern cap family commutes with flat pullback. -/
theorem flat : OperationalChow.CompatibleWithFlatPullback δ f (family f δ L) := sorry

/-- The first Chern cap family commutes with refined Cartier Gysin maps. -/
theorem gysin : OperationalChow.CompatibleWithCartierGysin δ f (family f δ L) := sorry

/-- The operational first Chern class acts by the first Chern cap of the pulled-back module. -/
def degree : OperationalChow δ f 1 :=
  OperationalChow.ofCap δ f (family f δ L) (proper f δ L) (flat f δ L) (gysin f δ L)

/-- The cap action of the operational first Chern class is the pulled-back first Chern cap. -/
theorem degree_cap {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (degree f δ L).cap g k =
      @FirstChernChow.lower S B Y _ _ (g ≫ f) _ _ δ _
        ((Modules.pullback g).obj L) (Modules.isInvertibleObject_pullback g L) k := rfl

/-- The degree-one homogeneous first Chern class in the operational Chow ring. -/
def ringClass : OperationalChow.ring δ f :=
  OperationalChow.homogeneous δ f 1 (degree f δ L)

/-- The operational first Chern class of a finite locally free module of rank one. -/
def rankOne (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 E] :
    OperationalChow δ f 1 :=
  degree f δ E

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
