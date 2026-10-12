/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Base
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.InverseSystem

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

open Scheme.FiniteTypeSeparatedOver Scheme.Modules
open RingedSpace.ModuleDerived

/-- The positive ideal-power system of global sections of `H⁰(K)`. -/
noncomputable def degreeZeroIdealPowerDiagram {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    OrderDual ℕ+ ⥤ ModuleCat.{u} k :=
  IdealPowerProduct.positiveSystem I
      (cohomologySheaf
        ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) 0) ⋙
    Scheme.Hom.globalSectionsFunctor (Over.hom X.obj)

/-- The degree-zero ideal-power diagram is obtained by applying global sections to the
positive ideal-power system of `H⁰(K)`. -/
theorem degreeZeroIdealPowerDiagram_def {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    degreeZeroIdealPowerDiagram X I K =
      IdealPowerProduct.positiveSystem I
          (cohomologySheaf
            ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) 0) ⋙
        Scheme.Hom.globalSectionsFunctor (Over.hom X.obj) := sorry

/-- The canonical degree-zero compact-support model associated to an ideal cutting out
the closed complement is the limit of the positive ideal-power diagram. -/
noncomputable def degreeZeroCompactSupport {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    ModuleCat.{u} k :=
  limit (degreeZeroIdealPowerDiagram X I K)

/-- The degree-zero compact-support model is the limit of its ideal-power diagram. -/
theorem degreeZeroCompactSupport_def {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    degreeZeroCompactSupport X I K =
      limit (degreeZeroIdealPowerDiagram X I K) := sorry

/-- The canonical degree-zero restriction map from the ideal-power compact-support model
to the global sections of `H⁰(K)`. -/
noncomputable def degreeZeroRestrictionMap {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    degreeZeroCompactSupport X I K →ₗ[k]
      Scheme.Hom.globalSectionsMod (Over.hom X.obj)
        (cohomologySheaf
          ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) 0) :=
  (limit.π (degreeZeroIdealPowerDiagram X I K) (OrderDual.toDual (1 : ℕ+)) ≫
    (Scheme.Hom.globalSectionsFunctor (Over.hom X.obj)).map
      ((IdealPowerFiltration.filtration I
        (cohomologySheaf
          ((ambient (SheafOfModules.isCoherent
            (Over.left X.obj).ringCatSheaf)).obj K) 0)).stage (1 : ℤ)).arrow).hom

/-- The degree-zero restriction map is projection to the first positive ideal-power stage,
followed by its canonical inclusion into `H⁰(K)`. -/
theorem degreeZeroRestrictionMap_def {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf]) :
    degreeZeroRestrictionMap X I K =
      (limit.π (degreeZeroIdealPowerDiagram X I K) (OrderDual.toDual (1 : ℕ+)) ≫
        (Scheme.Hom.globalSectionsFunctor (Over.hom X.obj)).map
          ((IdealPowerFiltration.filtration I
            (cohomologySheaf
              ((ambient (SheafOfModules.isCoherent
                (Over.left X.obj).ringCatSheaf)).obj K) 0)).stage (1 : ℤ)).arrow).hom := sorry

/-- The degree-zero compact-support restriction map attached to a morphism between chosen
compact-support presentations, followed by a proper-scheme comparison with global sections. -/
noncomputable def compactDegreeZeroRestrictionMap {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    {A B : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent
      (Over.left (base (Spec (CommRingCat.of k))).obj).ringCatSheaf]}
    (compactSystemMap : A ⟶ B)
    (properComparison :
      cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj) B 0 ≃ₗ[k]
        Scheme.Hom.globalSectionsMod (Over.hom X.obj)
          (cohomologySheaf
            ((ambient (SheafOfModules.isCoherent
              (Over.left X.obj).ringCatSheaf)).obj K) 0)) :
    cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj) A 0 →ₗ[k]
      Scheme.Hom.globalSectionsMod (Over.hom X.obj)
        (cohomologySheaf
          ((ambient (SheafOfModules.isCoherent
            (Over.left X.obj).ringCatSheaf)).obj K) 0) :=
  properComparison.toLinearMap.comp
    (cohomologyMap (Over.hom (base (Spec (CommRingCat.of k))).obj)
      compactSystemMap 0)

/-- The presentation comparison map is the compact-support cohomology map followed by the
proper-scheme comparison. -/
theorem compactDegreeZeroRestrictionMap_def {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    {A B : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent
      (Over.left (base (Spec (CommRingCat.of k))).obj).ringCatSheaf]}
    (compactSystemMap : A ⟶ B)
    (properComparison :
      cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj) B 0 ≃ₗ[k]
        Scheme.Hom.globalSectionsMod (Over.hom X.obj)
          (cohomologySheaf
            ((ambient (SheafOfModules.isCoherent
              (Over.left X.obj).ringCatSheaf)).obj K) 0)) :
    compactDegreeZeroRestrictionMap X K compactSystemMap properComparison =
      properComparison.toLinearMap.comp
        (cohomologyMap (Over.hom (base (Spec (CommRingCat.of k))).obj)
          compactSystemMap 0) := sorry

/-- Vanishing of a global section on an open neighborhood of a closed set is equivalent
to disjointness of its support from that closed set. -/
theorem vanishesOnOpenNeighborhood_iff_disjoint_sectionSupport {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (Z : TopologicalSpace.Closeds (Over.left X.obj : Scheme))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (s : Scheme.Hom.globalSectionsMod (Over.hom X.obj)
      (cohomologySheaf
        ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) 0)) :
    (∃ V : TopologicalSpace.Opens (Over.left X.obj : Scheme),
      (Z : Set (Over.left X.obj : Scheme)) ⊆ (V : Set (Over.left X.obj : Scheme)) ∧
        (RingedSpace.sectionFromTop
          (cohomologySheaf
            ((ambient (SheafOfModules.isCoherent
              (Over.left X.obj).ringCatSheaf)).obj K) 0) s).1
            (Opposite.op V) = 0) ↔
      Disjoint
        (SheafOfModules.sectionSupport
          (RingedSpace.sectionFromTop
            (cohomologySheaf
              ((ambient (SheafOfModules.isCoherent
                (Over.left X.obj).ringCatSheaf)).obj K) 0) s))
        (Z : Set (Over.left X.obj : Scheme)) := sorry

/-- For a proper scheme over a field and a bounded coherent complex with vanishing
negative cohomology, the canonical degree-zero compact-support restriction map is
injective. -/
theorem degreeZeroRestrictionMap_injective {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    [IsProper (Over.hom X.obj)]
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (h_negative : ∀ q < 0,
      IsZero (cohomologySheaf
        ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) q))
    (Z : TopologicalSpace.Closeds (Over.left X.obj : Scheme))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (h_ideal : I.openComplement = Z.compl) :
    Function.Injective (degreeZeroRestrictionMap X I K) := sorry

/-- The image of the canonical degree-zero compact-support restriction map consists
exactly of global sections of `H⁰(K)` that vanish on an open neighborhood of `Z`. -/
theorem range_degreeZeroRestrictionMap {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    [IsProper (Over.hom X.obj)]
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (h_negative : ∀ q < 0,
      IsZero (cohomologySheaf
        ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) q))
    (Z : TopologicalSpace.Closeds (Over.left X.obj : Scheme))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (h_ideal : I.openComplement = Z.compl) :
    Set.range (degreeZeroRestrictionMap X I K) =
      {s | ∃ V : TopologicalSpace.Opens (Over.left X.obj : Scheme),
        (Z : Set (Over.left X.obj : Scheme)) ⊆ (V : Set (Over.left X.obj : Scheme)) ∧
          (RingedSpace.sectionFromTop
            (cohomologySheaf
              ((ambient (SheafOfModules.isCoherent
              (Over.left X.obj).ringCatSheaf)).obj K) 0) s).1
          (Opposite.op V) = 0} := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
