module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Local

/-!
# Flattening loci along subsets of a closed fibre

This module represents flatness along a subset of the closed fibre by a closed subscheme
of an affine henselian local base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/-- Over an affine henselian local base, flatness of a finite-type quasicoherent module
along a subset of the closed fibre is represented by a closed subscheme. -/
theorem exists_closedImmersion_over_subset {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] [LocallyOfFiniteType f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)) (E : Set (f.fiber s)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
        ((∀ y : (pullback.snd f g).fiber t,
            pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ f.fiberι s '' E →
              flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                ((pullback.snd f g).fiberι t y)) ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)) := sorry

/-- If the morphism and module are finitely presented and the subset of the closed fibre
is closed and compact, its closed flattening subscheme can be chosen finitely presented. -/
theorem exists_closedImmersion_over_subset_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)) (E : Set (f.fiber s))
    (hE_closed : IsClosed E) (hE_compact : IsCompact E) :
    ∃ Z : Over S,
      (IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
          ((∀ y : (pullback.snd f g).fiber t,
              pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ f.fiberι s '' E →
                flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                  ((pullback.snd f g).fiberι t y)) ↔
            Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)) := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
