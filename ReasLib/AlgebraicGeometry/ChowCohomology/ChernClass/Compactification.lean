/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Proper
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.BivariantClass.Cospan.PushPull
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Integral
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Scheme.ProjectiveBundle.Compactification
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.ChernClass.Compactification

section Koszul

variable {X E : Scheme.{u}} (C : X.Modules) (π : E ⟶ X)
variable (hπ : Scheme.ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))

/-- The pullback of the vector-bundle module tensored with the inverse tautological line
on its projective compactification. -/
noncomputable def koszulModule : E.Modules :=
  (Scheme.Modules.pullback π).obj C ⊗
    (@isInvertibleObject.inverse E.Modules _ _
      (Scheme.ProjectiveBundle.tautologicalQuotient π hπ).object
      (Scheme.ProjectiveBundle.tautologicalQuotient π hπ).isInvertible)

/-- The Koszul map is the module-summand component of the tautological quotient,
tensored with the inverse tautological line and followed by evaluation. -/
noncomputable def koszulMap : koszulModule C π hπ ⟶ SheafOfModules.unit E.ringCatSheaf :=
  let q := Scheme.ProjectiveBundle.tautologicalQuotient π hπ
  let inverseLine := @isInvertibleObject.inverse E.Modules _ _ q.object q.isInvertible
  (((Scheme.Modules.pullback π).map biprod.inl ≫ q.hom) ▷ inverseLine) ≫
    (@isInvertibleObject.tensorInverseIso E.Modules _ _ q.object q.isInvertible).hom ≫
      RingedSpace.tensorUnitToUnitModule E.toRingedSpace

/-- The cochain Koszul complex on the canonical module-summand map has its `n`th exterior
power in cochain degree `-(n : ℤ)`. -/
noncomputable def koszulComplex : CochainComplex E.Modules ℤ :=
  (SheafOfModules.RingedSite.Koszul.complex E.sheaf (koszulMap C π hπ)).extend
    ComplexShape.embeddingDownNat

/-- Tensoring the pulled-back rank-`r` module with the inverse tautological line preserves
its finite local rank. -/
theorem koszulModule_rank (r : ℕ) [C.IsFiniteLocallyFreeOfRank r] :
    (koszulModule C π hπ).IsFiniteLocallyFreeOfRank r := sorry

/-- The canonical Koszul complex resolves the direct image of the structure module along
the zero section, regarded as a derived object concentrated in degree zero. -/
theorem koszulComplex_resolves (r : ℕ) [C.IsFiniteLocallyFreeOfRank r] :
    Nonempty ((DerivedCategory.Q.obj (koszulComplex C π hπ)) ≅
      (DerivedCategory.singleFunctor E.Modules 0).obj (zeroSectionModule C π hπ)) := sorry

end Koszul

variable {S X E : Scheme.{u}} [UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (p : X ⟶ S) [LocallyOfFiniteType p]
variable (C : X.Modules) (r : ℕ) [hC : C.IsFiniteLocallyFreeOfRank r]
variable (π : E ⟶ X)
variable (hπ : Scheme.ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))

/-- The total derived Chern series of the zero-section module is the finite alternating
product of the canonical Chern series of the exterior powers in its Koszul resolution. -/
noncomputable def totalClass :=
  let hE := ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1)
  let series : ℕ → @Nonnegative.Completion S E δ (π ≫ p)
      inferInstance inferInstance hE :=
    fun n t ↦ @ChowCohomology.ChernClass.component S E inferInstance δ inferInstance
      (π ≫ p) hE (Λ[n] (koszulModule C π hπ)) (Nat.choose r n)
      (@SheafOfModules.RingedSite.ExteriorPower.isFiniteLocallyFreeOfRank
        _ _ _ _ _ _ E.sheaf (koszulModule C π hπ) n inferInstance inferInstance r
          (koszulModule_rank C π hπ r)) t
  let factor := fun n ↦ if n % 2 = 0 then series n else
    @Nonnegative.Completion.formalInverse S E δ (π ≫ p) inferInstance inferInstance hE (series n)
  (List.range (r + 1)).foldl
    (fun acc n ↦ @Nonnegative.Completion.mul S E δ (π ≫ p)
      inferInstance inferInstance hE acc (factor n))
    (@Nonnegative.Completion.one S E δ (π ≫ p) inferInstance inferInstance hE)

/-- The degree-`t` derived Chern component of the zero-section module, computed from its
explicit Koszul resolution. -/
noncomputable def component (t : ℕ) := totalClass δ p C r π hπ t

/-- The derived Chern component is the corresponding coefficient of the finite alternating
canonical Chern series of the Koszul terms. -/
theorem component_def (t : ℕ) :
    component δ p C r π hπ t = totalClass δ p C r π hπ t := sorry

variable (V : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra C))
variable [hV : Scheme.IsRelativeSpectrumOver V]

/-- Applying the top derived Chern component, pushing along the projective projection,
and pulling along the vector-bundle projection gives a degree-zero cospan class. -/
noncomputable def pushPullComponent :=
  @BivariantClass.Cospan.pushPull S inferInstance δ inferInstance
    (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
    (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
      (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
    (ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1)) inferInstance
    (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π) r
    (@Scheme.AssociatedVectorBundle.overHomFlat S (Over.mk p) C
      (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
    (@Scheme.AssociatedVectorBundle.overHomRelativeDimension S (Over.mk p) C r hC V hV)
    (hπ.isProperOfFiniteLocallyFree r) (component δ p C r π hπ r)

/-- The specialized push-pull class has the cap family given by top Chern intersection,
proper pushforward, and relative-dimension-`r` flat pullback. -/
theorem pushPullComponent_def :
    @BivariantClass.Cospan.cap S inferInstance δ inferInstance
      _ _ _ _ _ _ _ _ 0 (pushPullComponent δ p C r π hπ V) =
      @BivariantClass.Cospan.pushPullCap S inferInstance δ inferInstance
        (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
        (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
          (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
        (ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1)) inferInstance
        (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π) r
        (@Scheme.AssociatedVectorBundle.overHomFlat S (Over.mk p) C
          (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
        (@Scheme.AssociatedVectorBundle.overHomRelativeDimension S (Over.mk p) C r hC V hV)
        (hπ.isProperOfFiniteLocallyFree r) (component δ p C r π hπ r) := sorry

/-- Flat pullback along the canonical vector-bundle inclusion, expressed as a degree-zero
class on the cospan of the two projections. -/
noncomputable def chartPullback :=
  @BivariantClass.Cospan.ofOverMorphism S inferInstance δ inferInstance
    (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
    (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
      (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
    (ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1)) inferInstance
    (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π)
    (jOver C V π hπ p) (jOver_projection C V π hπ p) 0
    (@BivariantClass.flatPullback S inferInstance δ inferInstance
      (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p))
      (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
        (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
      (ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1))
      (jOver C V π hπ p) 0 (j_flat C V π hπ) (j_relativeDimension C V π hπ))

/-- The chart pullback has the cospan cap family obtained from the ordinary bivariant
flat pullback along the canonical inclusion. -/
theorem chartPullback_def :
    @BivariantClass.Cospan.cap S inferInstance δ inferInstance
      _ _ _ _ _ _ _ _ 0 (chartPullback δ p C r π hπ V) =
      @BivariantClass.Cospan.ofOverMorphismCap S inferInstance δ inferInstance
        (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p)) (Over.mk p)
        (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
          (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
        (ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1)) inferInstance
        (Over.homMk (Scheme.associatedVectorBundleπ C V)) (Over.homMk π)
        (jOver C V π hπ p) (jOver_projection C V π hπ p) 0
        (@BivariantClass.flatPullback S inferInstance δ inferInstance
          (Over.mk (Scheme.associatedVectorBundleπ C V ≫ p)) (Over.mk (π ≫ p))
          (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S (Over.mk p) inferInstance C
            (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r C) V hV)
          (ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp hπ p (r + 1))
          (jOver C V π hπ p) 0 (j_flat C V π hπ) (j_relativeDimension C V π hπ)) := sorry

/-- The positive derived Chern components of the zero-section module vanish strictly below
the rank of the vector bundle. -/
theorem component_eq_zero (t : ℕ) (ht : 0 < t) (htr : t < r) :
    component δ p C r π hπ t = 0 := sorry

/-- The top derived Chern component of the zero-section module, followed by projective
pushforward and vector-bundle pullback, is the signed factorial multiple of chart pullback. -/
theorem pushPull_component (hr : 0 < r) :
    pushPullComponent δ p C r π hπ V =
      BivariantClass.Cospan.scale δ
        (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ))
        (chartPullback δ p C r π hπ V) := sorry

end AlgebraicGeometry.ChowCohomology.ChernClass.Compactification
