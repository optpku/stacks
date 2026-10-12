/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model.Comparison.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition compatibility for filtered right-derived comparisons

Compatible model comparisons compose along composable resolution maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Model.Comparison.IsCompatible

/-- Composite maps commute with the chosen stage comparisons. -/
@[stacks 0BKK "composition naturality of filtered right-derived model comparisons"]
theorem compStage {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} {m : KInjectiveResolution.Map f R S}
    {n : KInjectiveResolution.Map g S T} {P : Comparison F R}
    {Q : Comparison F S} {U : Comparison F T}
    (h : IsCompatible F m P Q) (k : IsCompatible F n Q U) :
    ∀ p a : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.stageMap
            (modelMap F (KInjectiveResolution.Map.comp m n)) p) a)
        (P.stageIso p a).hom (U.stageIso p a).hom
        (cochainCohomologyMap F (FilteredComplex.stageMap (f ≫ g) p) a) := sorry

/-- Composite maps commute with the chosen graded-piece comparisons. -/
@[stacks 0BKK "composition naturality of filtered right-derived model comparisons"]
theorem compGradedPiece {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} {m : KInjectiveResolution.Map f R S}
    {n : KInjectiveResolution.Map g S T} {P : Comparison F R}
    {Q : Comparison F S} {U : Comparison F T}
    (h : IsCompatible F m P Q) (k : IsCompatible F n Q U) :
    ∀ p a : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap
            (modelMap F (KInjectiveResolution.Map.comp m n)) p) a)
        (P.gradedPieceIso p a).hom (U.gradedPieceIso p a).hom
        (cochainCohomologyMap F (FilteredComplex.gradedPieceMap (f ≫ g) p) a) := sorry

/-- Composite maps commute with the chosen underlying-complex comparisons. -/
@[stacks 0BKK "composition naturality of filtered right-derived model comparisons"]
theorem compUnderlying {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} {m : KInjectiveResolution.Map f R S}
    {n : KInjectiveResolution.Map g S T} {P : Comparison F R}
    {Q : Comparison F S} {U : Comparison F T}
    (h : IsCompatible F m P Q) (k : IsCompatible F n Q U) :
    ∀ a : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap
            (modelMap F (KInjectiveResolution.Map.comp m n))) a)
        (P.underlyingIso a).hom (U.underlyingIso a).hom
        (cochainCohomologyMap F (FilteredComplex.underlyingMap (f ≫ g)) a) := sorry

/-- Composite naturality for chosen filtered right-derived model comparisons. -/
@[stacks 0BKK "composition of filtered right-derived model comparisons"]
theorem comp {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} {m : KInjectiveResolution.Map f R S}
    {n : KInjectiveResolution.Map g S T} {P : Comparison F R}
    {Q : Comparison F S} {U : Comparison F T}
    (h : IsCompatible F m P Q) (k : IsCompatible F n Q U) :
    IsCompatible F (KInjectiveResolution.Map.comp m n) P U := sorry

end Model.Comparison.IsCompatible

end CategoryTheory.FilteredComplex.RightDerived

