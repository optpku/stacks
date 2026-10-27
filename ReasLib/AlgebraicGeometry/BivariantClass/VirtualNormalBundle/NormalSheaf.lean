/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The normal sheaf has the same fixed finite rank as the conormal sheaf. -/
theorem normalSheaf_isFiniteLocallyFreeOfRank {Z X : Scheme.{u}} (i : Z ⟶ X)
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.normalSheaf i) := sorry

/-- The virtual normal bundle whose module is the normal sheaf and whose quotient map is a
chosen bidual identification with the conormal sheaf. -/
noncomputable def ofNormalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    VirtualNormalBundle i :=
  ofSurjection i (Scheme.Hom.normalSheaf i)
    (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      Z r (Scheme.Hom.normalSheaf i) (normalSheaf_isFiniteLocallyFreeOfRank i r))
    e.hom inferInstance

/-- The module of `ofNormalSheaf` has the prescribed fixed finite rank. -/
theorem ofNormalSheaf_module_isFiniteLocallyFreeOfRank
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (ofNormalSheaf i r e).module := by
  change Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.normalSheaf i)
  exact normalSheaf_isFiniteLocallyFreeOfRank i r

/-- The module of `ofNormalSheaf` is the normal sheaf. -/
theorem ofNormalSheaf_module {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (ofNormalSheaf i r e).module = Scheme.Hom.normalSheaf i := rfl

/-- The quotient map of `ofNormalSheaf` is the chosen bidual identification. -/
theorem ofNormalSheaf_map {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (ofNormalSheaf i r e).map = e.hom := rfl

/-- The degree-`r` bivariant class of the normal sheaf, formed from explicit deformation to
the normal cone data. -/
noncomputable def normalClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedDeformation (i ≫ p) p i rfl (ofNormalSheaf i r e)) :
    BivariantClass delta (overHom (i ≫ p) p i rfl) (r : ℤ) :=
  globalClassOfRank delta (i ≫ p) p i rfl (ofNormalSheaf i r e) D r

/-- The normal-sheaf class is the corresponding rank component of the virtual-normal class. -/
theorem normalClass_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedDeformation (i ≫ p) p i rfl (ofNormalSheaf i r e)) :
    normalClass delta p i r e D =
      globalClassOfRank delta (i ≫ p) p i rfl (ofNormalSheaf i r e) D r := rfl

/-- The normal sheaf of a morphism with finite locally free conormal sheaf is finite
locally free. -/
theorem normalSheaf_isFiniteLocallyFree {Z X : Scheme.{u}} (i : Z ⟶ X)
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)] :
    Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i) :=
  SheafOfModules.IsFiniteLocallyFree.of_iso (Scheme.Hom.normalSheafIsoDualConormal i).symm

/-- The normal virtual bundle of an immersion with finite locally free conormal sheaf,
using the inverse of canonical evaluation as its quotient map. -/
noncomputable def ofNormalSheafOfRankLoci {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)] :
    VirtualNormalBundle i :=
  ofSurjection i (Scheme.Hom.normalSheaf i) (normalSheaf_isFiniteLocallyFree i)
    (Scheme.Hom.bidualityIsoOfRankLoci i).hom inferInstance

/-- The canonical normal virtual bundle has the normal sheaf as its module. -/
theorem ofNormalSheafOfRankLoci_module {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)] :
    (ofNormalSheafOfRankLoci i).module = Scheme.Hom.normalSheaf i := rfl

/-- The quotient map of the canonical normal virtual bundle is inverse evaluation. -/
theorem ofNormalSheafOfRankLoci_map {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)] :
    (ofNormalSheafOfRankLoci i).map = (Scheme.Hom.bidualityIsoOfRankLoci i).hom := rfl

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
