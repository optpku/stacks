/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Local.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/- Lemma 38.24.3: over a henselian local affine base, flatness along a subset of the
closed fibre is represented by a closed subscheme. -/
@[stacks 05PI]
#check (AlgebraicGeometry.Scheme.Modules.Flattening.exists_closedImmersion_over_subset :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] [LocallyOfFiniteType f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)) (E : Set (f.fiber s)),
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
        ((∀ y : (pullback.snd f g).fiber t,
            pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ f.fiberι s '' E →
              flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                ((pullback.snd f g).fiberι t y)) ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)))

/- Under finite-presentation hypotheses and compactness of the closed subset, the
representing closed subscheme can be chosen finitely presented. -/
#check (AlgebraicGeometry.Scheme.Modules.Flattening.exists_closedImmersion_over_subset_of_finitePresentation :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)) (E : Set (f.fiber s))
    (hE_closed : IsClosed E) (hE_compact : IsCompact E),
    ∃ Z : Over S,
      (IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
          ((∀ y : (pullback.snd f g).fiber t,
              pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ f.fiberι s '' E →
                flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                  ((pullback.snd f g).fiberι t y)) ↔
            Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)))

end AlgebraicGeometry.Scheme.Modules.Flattening
