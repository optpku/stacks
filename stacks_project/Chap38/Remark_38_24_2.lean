module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Local
public import stacks_project.Chap38.«38_20_13_1_FlatFunctor»
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.Flattening

/- Remark 38.24.2 (1): over a henselian local affine base, the locus corepresenting
flatness of `ℱ` at the points of a pointed fibre mapping to `x` is a closed subscheme. -/
@[stacks 05PH] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.exists_closedImmersion_at :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules),
      [IsAffine S] → [HenselianLocalRing Γ(S, ⊤)] → [LocallyOfFiniteType f] →
      [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
      ∀ (x : X) (s : S), f x = s →
        S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤) →
          ∃ Z : Over S, IsClosedImmersion Z.hom ∧
            ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
              ((∀ y : (pullback.snd f g).fiber t,
                  pullback.fst f g ((pullback.snd f g).fiberι t y) = x →
                    flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                      ((pullback.snd f g).fiberι t y)) ↔
                Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)))

/- Remark 38.24.2 (2): if `f` and the stalk `ℱₓ` are finitely presented at `x`, the
closed flattening subscheme may be chosen finitely presented over the base. -/
@[stacks 05PH] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.exists_closedImmersion_at_of_finitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules),
      [IsAffine S] → [HenselianLocalRing Γ(S, ⊤)] → [LocallyOfFiniteType f] →
      [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
      ∀ (x : X) (s : S), f x = s →
        S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤) →
          f.FinitePresentationAt x →
            [Module.FinitePresentation (X.presheaf.stalk x)
              (RingedSpace.stalkModuleCat ℱ x)] →
              ∃ Z : Over S, IsClosedImmersion Z.hom ∧
                Scheme.Hom.FinitePresentation Z.hom ∧
                ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T), g t = s →
                  ((∀ y : (pullback.snd f g).fiber t,
                      pullback.fst f g ((pullback.snd f g).fiberι t y) = x →
                        flatOverAt (Scheme.Modules.baseChangeModule f g ℱ) (pullback.snd f g)
                          ((pullback.snd f g).fiberι t y)) ↔
                    Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z)))

end Scheme.Modules.Flattening
end AlgebraicGeometry
