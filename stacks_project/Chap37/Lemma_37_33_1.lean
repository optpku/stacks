module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.33.1: the locus where a finite locally free module descends along a flat,
proper, finitely presented morphism is represented by a finitely presented immersion. -/
@[stacks 0BDP] #check (AlgebraicGeometry.Scheme.Modules.existsDescentLocus :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom)),
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S) (_ : IsImmersion j)
      (_ : Scheme.Hom.FinitePresentation j),
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        Nonempty (Over.mk g ⟶ Over.mk j) ↔
          ∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree),
            Nonempty
              ((Scheme.Modules.pullback (pullback.snd f g)).obj N ≅
                (Scheme.Modules.pullback (pullback.fst f g)).obj E))

end AlgebraicGeometry.Scheme.Modules
