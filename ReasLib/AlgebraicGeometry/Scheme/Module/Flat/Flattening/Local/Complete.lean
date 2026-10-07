module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Local.Subset
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.RingTheory.Completion.Henselian

/-!
# Flattening loci over complete local bases

This module represents flatness along a closed fibre by a closed subscheme of
an affine Noetherian complete local base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/-- Over an affine Noetherian complete local base, flatness along the whole closed fibre
of a finite-type quasicoherent module is represented by a closed subscheme. -/
theorem exists_closedImmersion_over_closedFiber_of_completeLocal
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsCompleteLocalRing Γ(S, ⊤)]
    [Scheme.Hom.FiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
        ((∀ y : (pullback.snd f g).fiber t,
            pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ Set.range (f.fiberι s) →
              flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                ((pullback.snd f g).fiberι t y)) ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)) := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
