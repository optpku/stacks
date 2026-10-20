module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.BaseChange
import StacksCheckRecall

/-!
# Base change of quasi-compact morphisms of algebraic spaces

The base change of a quasi-compact morphism of algebraic spaces by any morphism
of algebraic spaces is again a quasi-compact morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.8.4: The base change of a quasi-compact morphism of algebraic spaces by
any morphism of algebraic spaces is quasi-compact. -/
@[stacks 03HF] #check (AlgebraicGeometry.AlgebraicSpace.quasiCompact_isStableUnderBaseChange : ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)))

#check
  (QuasiCompact.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
      QuasiCompact f → (g : Z ⟶ Y) → [HasPullback f g] →
        QuasiCompact (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
