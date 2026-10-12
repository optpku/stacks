/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

/- Lemma 49.9.4: in a cartesian square of Noetherian schemes with f flat and
quasi-finite, the different closed subscheme R of f and the different R' of the
base-changed morphism satisfy that Y' → Y induces a bijective closed immersion
R' → R ×_Y Y'; if g is flat or ω_{Y/X} is invertible, then R' equals that
pullback. -/
@[stacks 0BW7] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.baseChangeComparison_isClosedImmersion :
    ∀ {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
      [Flat f] [Scheme.Hom.QuasiFinite f] [Flat f'] [Scheme.Hom.QuasiFinite f']
      (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
      (g : X' ⟶ X) (h : Y' ⟶ Y)
      (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
      (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
      (hτ' : W'.IsTraceSection τ'),
      IsClosedImmersion
        (W.baseChangeComparison W' h τ τ'
          (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.comap_le_of_isPullback
            W W' g h τ τ' sq hτ hτ')))

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.baseChange_bijective :
    ∀ {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
      [Flat f] [Scheme.Hom.QuasiFinite f] [Flat f'] [Scheme.Hom.QuasiFinite f']
      (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
      (g : X' ⟶ X) (h : Y' ⟶ Y)
      (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
      (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
      (hτ' : W'.IsTraceSection τ'),
      Function.Bijective ⇑(ConcreteCategory.hom
        (W.baseChangeComparison W' h τ τ'
          (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.comap_le_of_isPullback
            W W' g h τ τ' sq hτ hτ')).base))

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.baseChange_eq_of_flat_or_isInvertible :
    ∀ {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
      [Flat f] [Scheme.Hom.QuasiFinite f] [Flat f'] [Scheme.Hom.QuasiFinite f']
      (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
      (g : X' ⟶ X) (h : Y' ⟶ Y)
      (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
      (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
      (hτ' : W'.IsTraceSection τ'),
      Flat g ∨ Scheme.Modules.Invertible W.module.obj →
        W'.different τ' = (W.different τ).comap h)
