/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Differential

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Scheme.Hom
  Scheme.Hom.LocalCohomology

universe u

namespace AlgebraicGeometry
namespace Scheme.DeRham.Gysin

variable {Z X S : Scheme.{u}}

/-- The source comparison from restricted ambient forms to an equation presentation is an
epimorphism. -/
theorem equationGysinSourceComparison_epi (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p : ℕ) (P : EquationPresentation i c) :
    Epi (equationGysinSourceComparison i f c p P) := sorry

/-- The target comparison for an equation presentation is invertible. -/
theorem equationGysinTargetComparison_isIso (i : Z ⟶ X)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (P : EquationPresentation i c) :
    IsIso (equationGysinTargetComparison i f c p P) := sorry

/-- The evaluated global Gysin map, transported back through the equation target comparison,
kills the kernel of the equation source comparison. -/
theorem mapOfClosedImmersion_killsEquationSourceKernel (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (P : EquationPresentation i c) :
    kernel.ι (equationGysinSourceComparison i f c p P) ≫
        (forget₂ _ _).map
          (((Scheme.Modules.pushforward i).map
            (pullbackFormToClosedForm i f p)).val.app (op P.carrier)) ≫
        (forget₂ _ _).map
          ((mapOfClosedImmersion i f c p).val.app (op P.carrier)) ≫
        @inv _ _ _ _ (equationGysinTargetComparison i f c (p + c) P)
          (equationGysinTargetComparison_isIso i f c (p + c) P) = 0 := sorry

/-- On an equation presentation of a finitely presented closed immersion, the degree-`p`
and degree-`p + 1` components of the Gysin morphism commute with the relative de Rham
differentials and the canonical degree transport. -/
theorem mapOfClosedImmersion_d (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (P : EquationPresentation i c) :
    @Abelian.epiDesc _ _ _ _ _ (equationGysinSourceComparison i f c p P)
          (equationGysinSourceComparison_epi i f c p P) _
          ((forget₂ _ _).map
              (((Scheme.Modules.pushforward i).map
                (pullbackFormToClosedForm i f p)).val.app (op P.carrier)) ≫
            (forget₂ _ _).map
              ((mapOfClosedImmersion i f c p).val.app (op P.carrier)) ≫
            @inv _ _ _ _ (equationGysinTargetComparison i f c (p + c) P)
              (equationGysinTargetComparison_isIso i f c (p + c) P))
          (mapOfClosedImmersion_killsEquationSourceKernel i f c p P) ≫
        (forget₂ _ _).map
          ((targetDifferential (P.carrier.ι ≫ f) P.generators (p + c)).val.app (op ⊤)) =
      (forget₂ _ _).map
          ((sourceDifferential (P.carrier.ι ≫ f) P.generators p).val.app (op ⊤)) ≫
        @Abelian.epiDesc _ _ _ _ _ (equationGysinSourceComparison i f c (p + 1) P)
          (equationGysinSourceComparison_epi i f c (p + 1) P) _
          ((forget₂ _ _).map
              (((Scheme.Modules.pushforward i).map
                (pullbackFormToClosedForm i f (p + 1))).val.app (op P.carrier)) ≫
            (forget₂ _ _).map
              ((mapOfClosedImmersion i f c (p + 1)).val.app (op P.carrier)) ≫
            @inv _ _ _ _ (equationGysinTargetComparison i f c ((p + 1) + c) P)
              (equationGysinTargetComparison_isIso i f c ((p + 1) + c) P))
          (mapOfClosedImmersion_killsEquationSourceKernel i f c (p + 1) P) ≫
        (forget₂ _ _).map
          ((eqToHom (congrArg (restrictedTarget (P.carrier.ι ≫ f) P.generators)
            (Nat.add_right_comm p 1 c))).val.app (op ⊤)) := sorry

end Scheme.DeRham.Gysin
end AlgebraicGeometry

end
