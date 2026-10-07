module

public import ReasLib.AlgebraicGeometry.RelativePurity.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 38.16.6 (1): purity along a fibre descends from a pointed base change that is
flat at the selected point. -/
@[stacks 05J9] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.of_pullback_of_flatAt :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S'), g s' = s → g.flatAt s' →
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
        (pullback.snd f g) s' → F.IsPureAlong f s)

/- Companion clause (2): universal purity along a fibre descends from a pointed base change
that is flat at the selected point. -/
#check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureAlong.of_pullback_of_flatAt :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S'), g s' = s → g.flatAt s' →
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsUniversallyPureAlong
        (pullback.snd f g) s' → F.IsUniversallyPureAlong f s)

end AlgebraicGeometry
