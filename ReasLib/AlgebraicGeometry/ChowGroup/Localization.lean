/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.Localization

/-!
# Localization of Chow groups at an open subscheme

This file defines the fixed-degree Chow-group maps associated to an open subscheme and its
reduced closed complement, packages them as a short complex, and states its exactness.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.Localization

/-- If two cycles restrict to rationally equivalent cycles on an open subscheme, their
difference is rationally equivalent to a cycle pushed forward from the reduced complement. -/
theorem exists_closedPushforward {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : X.Opens) (k : ℤ) (α β : CycleGroup X (p.relativeDimensionFunction δ) k)
    (h : @RationalEquivalence.RationallyEquivalent U.toScheme
      (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
      ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k
      (openPullback p δ U k α) (openPullback p δ U k β)) :
    ∃ γ : CycleGroup (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme
        (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
        k,
      @RationalEquivalence.RationallyEquivalent X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k α
        (β + closedPushforward p δ U k γ) := sorry

end AlgebraicGeometry.CycleGroup.Localization

namespace AlgebraicGeometry.ChowGroup.Localization

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]

/-- Open restriction carries rational boundaries to rational boundaries. -/
theorem openPullback_mem_boundaries (U : X.Opens) (k : ℤ) :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k ≤
      (@RationalEquivalence.boundaries U.toScheme
        (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
        ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k).comap
        (CycleGroup.Localization.openPullback p δ U k) := sorry

/-- Pushforward from the reduced closed complement on degree-`k` Chow groups. -/
noncomputable def closedPushforward (U : X.Opens) (k : ℤ) :
    @ChowGroup (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme
        (LocallyOfFiniteType.isLocallyNoetherian
          ((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p))
        (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
        inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  @ChowGroup.map S inferInstance δ inferInstance
    (Over.mk ((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p)) (Over.mk p)
    (inferInstanceAs (LocallyOfFiniteType
      ((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p)))
    (inferInstanceAs (LocallyOfFiniteType p))
    (Over.homMk (Scheme.ClosedSubschemeStructure.reduced U.compl).ι rfl)
    (inferInstanceAs (IsProper (Scheme.ClosedSubschemeStructure.reduced U.compl).ι)) k

/-- Closed-complement pushforward on a Chow class is induced by cycle pushforward. -/
theorem closedPushforward_chowClass (U : X.Opens) (k : ℤ)
    (γ : CycleGroup (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme
      (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
      k) :
    Localization.closedPushforward p δ U k
        (@chowClass (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme
          (LocallyOfFiniteType.isLocallyNoetherian
            ((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p))
          (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
          inferInstance k γ) =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (CycleGroup.Localization.closedPushforward p δ U k γ) := sorry

/-- Restriction to an open subscheme on degree-`k` Chow groups. -/
noncomputable def openPullback (U : X.Opens) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup U.toScheme (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
        ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k)
    (@RationalEquivalence.boundaries U.toScheme
      (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
      ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k)
    (CycleGroup.Localization.openPullback p δ U k)
    (openPullback_mem_boundaries p δ U k)

/-- Open pullback on a Chow class is induced by coefficientwise cycle restriction. -/
theorem openPullback_chowClass (U : X.Opens) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    Localization.openPullback p δ U k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) =
      @chowClass U.toScheme (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
        ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k
        (CycleGroup.Localization.openPullback p δ U k α) := sorry

/-- Closed-complement pushforward followed by open pullback is zero on Chow groups. -/
theorem closedPushforward_comp_openPullback (U : X.Opens) (k : ℤ) :
    AddCommGrpCat.ofHom (Localization.closedPushforward p δ U k) ≫
      AddCommGrpCat.ofHom (Localization.openPullback p δ U k) = 0 := sorry

/-- The localization short complex of degree-`k` Chow groups associated to an open subscheme. -/
noncomputable def complex (U : X.Opens) (k : ℤ) : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (Localization.closedPushforward p δ U k))
    (AddCommGrpCat.ofHom (Localization.openPullback p δ U k))
    (closedPushforward_comp_openPullback p δ U k)

/-- The first arrow in the Chow localization complex is closed-complement pushforward. -/
theorem complex_f (U : X.Opens) (k : ℤ) :
    (Localization.complex p δ U k).f =
      AddCommGrpCat.ofHom (Localization.closedPushforward p δ U k) := sorry

/-- The second arrow in the Chow localization complex is open pullback. -/
theorem complex_g (U : X.Opens) (k : ℤ) :
    (Localization.complex p δ U k).g =
      AddCommGrpCat.ofHom (Localization.openPullback p δ U k) := sorry

/-- The Chow localization complex is exact at the ambient scheme, and restriction to the open
subscheme is an epimorphism. -/
theorem exact {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : X.Opens) (k : ℤ) :
    (complex p δ U k).Exact ∧ Epi (complex p δ U k).g := sorry

/-- Restriction to an open subscheme is canonically an epimorphism on Chow groups. -/
instance openPullback_epi (U : X.Opens) (k : ℤ) :
    Epi (Localization.complex p δ U k).g := sorry

end AlgebraicGeometry.ChowGroup.Localization
