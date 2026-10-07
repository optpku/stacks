module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.OpenPullback
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

/-!
# Localization of cycle groups at an open subscheme

This file defines the fixed-degree cycle-group maps associated to an open subscheme and its
reduced closed complement, packages them as a short complex, and states its exactness.
-/

@[expose] public section

open CategoryTheory Function

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.Localization

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]

/-- Restriction to an open subscheme preserves the relative degree of cycles. -/
theorem openPullback_mem_dimensionSubgroup (U : X.Opens) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    AlgebraicCycle.openPullback U
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k α) ∈
      AlgebraicCycle.dimensionSubgroup ((U.ι ≫ p).relativeDimensionFunction δ) k := sorry

/-- The value of coefficientwise restriction on a cycle of fixed relative degree. -/
noncomputable def openPullbackValue (U : X.Opens) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    CycleGroup U.toScheme ((U.ι ≫ p).relativeDimensionFunction δ) k :=
  ⟨AlgebraicCycle.openPullback U
      (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k α),
    openPullback_mem_dimensionSubgroup p δ U k α⟩

/-- Coefficientwise restriction sends the zero cycle to zero. -/
theorem openPullbackValue_zero (U : X.Opens) (k : ℤ) :
    openPullbackValue p δ U k 0 = 0 := sorry

/-- Coefficientwise restriction preserves addition of cycles. -/
theorem openPullbackValue_add (U : X.Opens) (k : ℤ)
    (α β : CycleGroup X (p.relativeDimensionFunction δ) k) :
    openPullbackValue p δ U k (α + β) =
      openPullbackValue p δ U k α + openPullbackValue p δ U k β := sorry

/-- Pullback of cycles of fixed relative degree to an open subscheme. -/
noncomputable def openPullback (U : X.Opens) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) k →+
      CycleGroup U.toScheme ((U.ι ≫ p).relativeDimensionFunction δ) k where
  toFun := openPullbackValue p δ U k
  map_zero' := openPullbackValue_zero p δ U k
  map_add' := openPullbackValue_add p δ U k

/-- Open pullback restricts the coefficient function along the canonical open immersion. -/
theorem openPullback_apply (U : X.Opens) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) (u : U.toScheme) :
    CycleGroup.toAlgebraicCycle ((U.ι ≫ p).relativeDimensionFunction δ) k
        (openPullback p δ U k α) u =
      CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k α (U.ι u) := sorry

/-- Open pullback on cycles of fixed relative degree is surjective. -/
theorem openPullback_surjective (U : X.Opens) (k : ℤ) :
    Function.Surjective (openPullback p δ U k) := sorry

/-- Open pullback is canonically an epimorphism of abelian groups. -/
instance openPullback_epi (U : X.Opens) (k : ℤ) :
    Epi (AddCommGrpCat.ofHom (openPullback p δ U k)) := sorry

/-- Pushforward of cycles of fixed relative degree from the reduced closed complement of an open
subscheme. -/
noncomputable def closedPushforward (U : X.Opens) (k : ℤ) :
    CycleGroup (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme
        (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
        k →+
      CycleGroup X (p.relativeDimensionFunction δ) k :=
  CycleGroup.mapHom (Scheme.ClosedSubschemeStructure.reduced U.compl).ι
    (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
    (p.relativeDimensionFunction δ) k

/-- Closed-complement pushforward is the usual pushforward of algebraic cycles. -/
theorem closedPushforward_apply (U : X.Opens) (k : ℤ)
    (α : CycleGroup (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme
      (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ) k)
    (x : X) :
    CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (closedPushforward p δ U k α) x =
      AlgebraicCycle.map (Scheme.ClosedSubschemeStructure.reduced U.compl).ι
        (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
        (p.relativeDimensionFunction δ)
        (CycleGroup.toAlgebraicCycle
          (((Scheme.ClosedSubschemeStructure.reduced U.compl).ι ≫ p).relativeDimensionFunction δ)
          k α) x := sorry

/-- Pushforward from the reduced closed complement followed by restriction to the open subscheme
is zero. -/
theorem closedPushforward_comp_openPullback (U : X.Opens) (k : ℤ) :
    AddCommGrpCat.ofHom (closedPushforward p δ U k) ≫
      AddCommGrpCat.ofHom (openPullback p δ U k) = 0 := sorry

/-- The localization short complex of cycle groups of fixed relative degree associated to an open
subscheme. -/
noncomputable def complex (U : X.Opens) (k : ℤ) : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (closedPushforward p δ U k))
    (AddCommGrpCat.ofHom (openPullback p δ U k))
    (closedPushforward_comp_openPullback p δ U k)

/-- The first arrow in the localization complex is reduced closed-complement pushforward. -/
theorem complex_f (U : X.Opens) (k : ℤ) :
    (complex p δ U k).f = AddCommGrpCat.ofHom (closedPushforward p δ U k) := sorry

/-- The second arrow in the localization complex is open pullback. -/
theorem complex_g (U : X.Opens) (k : ℤ) :
    (complex p δ U k).g = AddCommGrpCat.ofHom (openPullback p δ U k) := sorry

/-- The localization complex for an open subscheme and its reduced closed complement is exact at
the ambient cycle group, and its open-pullback arrow is an epimorphism. -/
theorem exact {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : X.Opens) (k : ℤ) :
    (complex p δ U k).Exact ∧ Epi (complex p δ U k).g := sorry

end AlgebraicGeometry.CycleGroup.Localization
