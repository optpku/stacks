/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CoherentBounded
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat.Limits

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Cohomology

/-- Bounded coherent derived cohomology over an affine field base, obtained by shifting,
pushing forward along a quasi-compact quasi-separated morphism, taking affine derived
global sections, and extracting homology in degree `0`. -/
noncomputable def overFieldFunctor {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p] (i : ℤ) :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤ ModuleCat.{u} k :=
  DerivedQCoh.coherentBoundedToDerivedQCoh X ⋙
    shiftFunctor (DerivedQCoh X) i ⋙ DerivedQCoh.pushforwardCohomologyIn p ⋙
      DerivedQCoh.affineGlobalSections (CommRingCat.of k) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0

/-- The cohomology object in degree `i` over the field base. -/
noncomputable abbrev overField {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) : ModuleCat.{u} k :=
  (overFieldFunctor p i).obj K

/-- `overField` is the value of the bounded coherent cohomology functor. -/
theorem overField_def {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    overField p K i = (overFieldFunctor p i).obj K := rfl

end AlgebraicGeometry.Scheme.ModuleDerived.Cohomology

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

/-- The module-valued cohomology inverse system of a bounded coherent compact-support
presentation over a field. -/
noncomputable def cohomologyDiagram {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    PNatInverseSystem (ModuleCat.{u} k) :=
  A ⋙ Cohomology.overFieldFunctor p i

/-- A stage of the compact-support cohomology diagram is the cohomology of the
corresponding presentation stage. -/
theorem cohomologyDiagram_stage {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (i : ℤ) (n : ℕ+) :
    (cohomologyDiagram p A i).stage n = Cohomology.overField p (A.stage n) i := rfl

/-- Compactly supported cohomology represented by a chosen positive inverse system. -/
noncomputable abbrev cohomology {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    ModuleCat.{u} k :=
  limit (cohomologyDiagram p A i)

/-- Compactly supported cohomology is the limit of the stagewise cohomology diagram. -/
theorem cohomology_def {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    cohomology p A i = limit (cohomologyDiagram p A i) := rfl

/-- The inverse-limit topology on a chosen compact-support cohomology presentation. -/
@[implicit_reducible]
noncomputable def cohomologyTopology {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    TopologicalSpace (cohomology p A i) :=
  CategoryTheory.Functor.limitTopology (cohomologyDiagram p A i)

/-- The topology on compactly supported cohomology is the limit topology of its
presentation. -/
theorem cohomologyTopology_def {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    cohomologyTopology p A i =
      CategoryTheory.Functor.limitTopology (cohomologyDiagram p A i) := rfl

/-- A morphism of compact-support presentations induces the corresponding linear map on
cohomology limits. -/
noncomputable def cohomologyMap {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    {A B : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]}
    (f : A ⟶ B) (i : ℤ) : cohomology p A i →ₗ[k] cohomology p B i :=
  (limMap (Functor.whiskerRight f (Cohomology.overFieldFunctor p i))).hom

/-- The cohomology map is the limit map induced by the stagewise cohomology maps. -/
theorem cohomologyMap_def {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    {A B : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]}
    (f : A ⟶ B) (i : ℤ) :
    cohomologyMap p f i =
      (limMap (Functor.whiskerRight f (Cohomology.overFieldFunctor p i))).hom := rfl

/-- Compact-support cohomology maps preserve identity morphisms. -/
theorem cohomologyMap_id {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    (A : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (i : ℤ) :
    cohomologyMap p (𝟙 A) i = LinearMap.id := by
  unfold cohomologyMap
  rw [Functor.whiskerRight_id']
  exact congrArg (fun f : cohomology p A i ⟶ cohomology p A i ↦ f.hom)
    ((lim : (OrderDual ℕ+ ⥤ ModuleCat.{u} k) ⥤ ModuleCat.{u} k).map_id _)

/-- Compact-support cohomology maps preserve composition. -/
theorem cohomologyMap_comp {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact p] [QuasiSeparated p]
    {A B C : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]}
    (f : A ⟶ B) (g : B ⟶ C) (i : ℤ) :
    cohomologyMap p (f ≫ g) i = (cohomologyMap p g i).comp (cohomologyMap p f i) := by
  unfold cohomologyMap
  rw [Functor.whiskerRight_comp]
  exact congrArg (fun h : cohomology p A i ⟶ cohomology p C i ↦ h.hom)
    ((lim : (OrderDual ℕ+ ⥤ ModuleCat.{u} k) ⥤ ModuleCat.{u} k).map_comp
      (Functor.whiskerRight f (Cohomology.overFieldFunctor p i))
      (Functor.whiskerRight g (Cohomology.overFieldFunctor p i)))

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
