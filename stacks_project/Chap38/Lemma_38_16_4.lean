module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativePurity

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 38.16.4: purity along a fibre is preserved by a pointed base change that is
quasi-finite at the selected point. -/
@[stacks 05J7] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.pullback_of_quasiFiniteAt :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S'), g s' = s →
        Scheme.Hom.FiniteType.QuasiFiniteAt g s' → F.IsPureAlong f s →
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
            (pullback.snd f g) s')
