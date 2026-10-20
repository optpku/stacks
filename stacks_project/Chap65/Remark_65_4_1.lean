module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

/- Remark 65.4.1: these morphism properties of schemes are stable under arbitrary base change. -/
@[stacks 02WF] #check
  (AlgebraicGeometry.Scheme.Hom.baseChange_properties :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S),
    (IsClosedImmersion f → IsClosedImmersion (pullback.snd f g)) ∧
    (IsOpenImmersion f → IsOpenImmersion (pullback.snd f g)) ∧
    (IsImmersion f → IsImmersion (pullback.snd f g)) ∧
    (QuasiCompact f → QuasiCompact (pullback.snd f g)) ∧
    (UniversallyClosed f → UniversallyClosed (pullback.snd f g)) ∧
    (IsSeparated f → IsSeparated (pullback.snd f g)) ∧
    (QuasiSeparated f → QuasiSeparated (pullback.snd f g)) ∧
    (Mono f → Mono (pullback.snd f g)) ∧
    (Surjective f → Surjective (pullback.snd f g)) ∧
    (UniversallyInjective f → UniversallyInjective (pullback.snd f g)) ∧
    (IsAffineHom f → IsAffineHom (pullback.snd f g)) ∧
    (QuasiAffineHom f → QuasiAffineHom (pullback.snd f g)) ∧
    (LocallyOfFiniteType f → LocallyOfFiniteType (pullback.snd f g)) ∧
    (Scheme.Hom.FiniteType f → Scheme.Hom.FiniteType (pullback.snd f g)) ∧
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f →
      LocallyOfFiniteType (pullback.snd f g) ∧ LocallyQuasiFinite (pullback.snd f g)) ∧
    (Scheme.Hom.QuasiFinite f → Scheme.Hom.QuasiFinite (pullback.snd f g)) ∧
    (LocallyOfFinitePresentation f → LocallyOfFinitePresentation (pullback.snd f g)) ∧
    (Scheme.Hom.FinitePresentation f → Scheme.Hom.FinitePresentation (pullback.snd f g)) ∧
    (∀ d : ℕ, Scheme.Hom.RelativeDimension f d →
      Scheme.Hom.RelativeDimension (pullback.snd f g) d) ∧
    (UniversallyOpen f → UniversallyOpen (pullback.snd f g)) ∧
    (Flat f → Flat (pullback.snd f g)) ∧
    (Syntomic f → Syntomic (pullback.snd f g)) ∧
    (Smooth f → Smooth (pullback.snd f g)) ∧
    (Unramified f → Unramified (pullback.snd f g)) ∧
    (GUnramified f → GUnramified (pullback.snd f g)) ∧
    (Etale f → Etale (pullback.snd f g)) ∧
    (IsProper f → IsProper (pullback.snd f g)) ∧
    (HProjective f → HProjective (pullback.snd f g)) ∧
    (Projective f → Projective (pullback.snd f g)) ∧
    (LocallyProjective f → LocallyProjective (pullback.snd f g)) ∧
    (IsFinite f → IsFinite (pullback.snd f g)) ∧
    (IsIntegralHom f → IsIntegralHom (pullback.snd f g)) ∧
    (IsFiniteLocallyFree f → IsFiniteLocallyFree (pullback.snd f g)) ∧
    (UniversallySubmersive f → UniversallySubmersive (pullback.snd f g)) ∧
    (UniversalHomeomorphism f → UniversalHomeomorphism (pullback.snd f g)))
