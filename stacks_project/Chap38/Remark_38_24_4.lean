module

import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Local.Complete
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/- Remark 38.24.4: if `f` and `ℱ` are of finite type, `E` is the whole closed
fibre, and the base is the spectrum of a Noetherian complete local ring, the
closed flattening subscheme of Lemma 38.24.3 can alternatively be constructed
after passing to a finite affine open cover. In the affine case it is built over
the Artinian truncations by powers of the maximal ideal and then recovered from
their inverse limit. -/
@[stacks 052G] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.exists_closedImmersion_over_closedFiber_of_completeLocal :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
      [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsCompleteLocalRing Γ(S, ⊤)]
      [Scheme.Hom.FiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
      (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)),
      ∃ Z : Over S, IsClosedImmersion Z.hom ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
          ((∀ y : (pullback.snd f g).fiber t,
              pullback.fst f g ((pullback.snd f g).fiberι t y) ∈ Set.range (f.fiberι s) →
                flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                  ((pullback.snd f g).fiberι t y)) ↔
            Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)))

end AlgebraicGeometry.Scheme.Modules.Flattening
