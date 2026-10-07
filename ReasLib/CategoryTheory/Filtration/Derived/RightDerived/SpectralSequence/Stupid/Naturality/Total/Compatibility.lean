module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total.PageOne
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Forget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility of stupid total projections

The stupid specialization is a reindexing of the generic realization layer.  These functor
equalities keep that relationship available without unfolding the displayed total construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- The stupid filtered-model projection is the generic projection after `genericFunctor`. -/
@[stacks 0FLK "generic filtered projection of stupid total realizations"]
theorem genericFunctor_forgetFiltered :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetFiltered F =
      forgetFiltered F := sorry

/-- The stupid spectral-sequence projection is the generic projection after `genericFunctor`. -/
@[stacks 0FLK "generic sequence projection of stupid total realizations"]
theorem genericFunctor_forgetSequence :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetSequence F =
      forgetSequence F := sorry

/-- The stupid underlying-complex projection is the generic projection after `genericFunctor`. -/
@[stacks 0FLK "generic underlying projection of stupid total realizations"]
theorem genericFunctor_forgetUnderlying :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.forgetUnderlying F =
      forgetUnderlying F := sorry

/-- The generic graded-piece target and the specialized termwise right-derived target are
canonically isomorphic on total stupid realizations.  The comparison is relative to the two
page-one identifications stored by the realization, so it introduces no additional choice. -/
@[stacks 0FLK "generic target comparison for total stupid first pages"]
noncomputable def genericFunctor_pageOneTargetIso (p : ℤ) (q : ℕ) :
    genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.pageOneTarget
          F p (Int.ofNat q) ≅
      pageOneTarget F p q :=
  (Functor.isoWhiskerLeft (genericFunctor F)
      (RightDerived.SpectralSequence.Realization.Total.pageOneComparison
        F p (Int.ofNat q))).symm ≪≫
    pageOneComparison F p q

/-- The target comparison component is the composite of the inverse generic page-one
identification and the specialized page-one identification. -/
@[simp, stacks 0FLK "component of the generic target comparison for stupid first pages"]
theorem genericFunctor_pageOneTargetIso_app (p : ℤ) (q : ℕ)
    (S : Realization.Total F) :
    (genericFunctor_pageOneTargetIso F p q).app S =
      (S.obj.original.pageOneIso p (Int.ofNat q)).symm ≪≫
        S.obj.pageOneIso p q := sorry

/-- The forward component of the target comparison first inverts the generic page-one
identification and then applies the specialized one. -/
@[simp, stacks 0FLK "forward generic target comparison for stupid first pages"]
theorem genericFunctor_pageOneTargetIso_hom_app (p : ℤ) (q : ℕ)
    (S : Realization.Total F) :
    (genericFunctor_pageOneTargetIso F p q).hom.app S =
      (S.obj.original.pageOneIso p (Int.ofNat q)).inv ≫
        (S.obj.pageOneIso p q).hom := sorry

/-- The inverse component of the target comparison first inverts the specialized page-one
identification and then applies the generic one. -/
@[simp, stacks 0FLK "inverse generic target comparison for stupid first pages"]
theorem genericFunctor_pageOneTargetIso_inv_app (p : ℤ) (q : ℕ)
    (S : Realization.Total F) :
    (genericFunctor_pageOneTargetIso F p q).inv.app S =
      (S.obj.pageOneIso p q).inv ≫
        (S.obj.original.pageOneIso p (Int.ofNat q)).hom := sorry

/-- The generic target comparison is natural for total stupid-realization morphisms. -/
@[reassoc, stacks 0FLK "naturality of the generic target comparison for stupid first pages"]
theorem genericFunctor_pageOneTargetIso_hom_naturality (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneTarget
            F p (Int.ofNat q)).map m ≫
        (genericFunctor_pageOneTargetIso F p q).hom.app T =
      (genericFunctor_pageOneTargetIso F p q).hom.app S ≫
        (pageOneTarget F p q).map m := sorry

/-- The inverse generic target comparison is natural for total stupid-realization morphisms. -/
@[reassoc, stacks 0FLK
  "inverse naturality of the generic target comparison for stupid first pages"]
theorem genericFunctor_pageOneTargetIso_inv_naturality (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (pageOneTarget F p q).map m ≫
        (genericFunctor_pageOneTargetIso F p q).inv.app T =
      (genericFunctor_pageOneTargetIso F p q).inv.app S ≫
        (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneTarget
            F p (Int.ofNat q)).map m := sorry

/-- Conjugating the specialized target map by the target comparison recovers the generic
graded-piece target map. -/
@[reassoc, stacks 0FLK "generic target-map computation for total stupid first pages"]
theorem genericFunctor_pageOneTargetIso_source_map (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor_pageOneTargetIso F p q).hom.app S ≫
        (pageOneTarget F p q).map m ≫
        (genericFunctor_pageOneTargetIso F p q).inv.app T =
      (genericFunctor F ⋙
        RightDerived.SpectralSequence.Realization.Total.pageOneTarget
          F p (Int.ofNat q)).map m := sorry

/-- Conjugating the generic graded-piece target map by the inverse target comparison recovers
the specialized target map. -/
@[reassoc, stacks 0FLK "specialized target-map computation for total stupid first pages"]
theorem genericFunctor_pageOneTargetIso_target_map (p : ℤ) (q : ℕ)
    {S T : Realization.Total F} (m : S ⟶ T) :
    (genericFunctor_pageOneTargetIso F p q).inv.app S ≫
        (genericFunctor F ⋙
          RightDerived.SpectralSequence.Realization.Total.pageOneTarget
            F p (Int.ofNat q)).map m ≫
        (genericFunctor_pageOneTargetIso F p q).hom.app T =
      (pageOneTarget F p q).map m := sorry

/-- Composing the generic page-one comparison with the target comparison recovers the
specialized page-one comparison. -/
@[stacks 0FLK "compatibility of generic and specialized total stupid first pages"]
theorem pageOneComparison_compat (p : ℤ) (q : ℕ) :
    Functor.isoWhiskerLeft (genericFunctor F)
          (RightDerived.SpectralSequence.Realization.Total.pageOneComparison
            F p (Int.ofNat q)) ≪≫
        genericFunctor_pageOneTargetIso F p q =
      pageOneComparison F p q := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
