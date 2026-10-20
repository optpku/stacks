module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of scheme-module pushforward

The ambient `Scheme.Modules` pushforward comparisons form the reusable
composition and identity coherence layer.  Quasi-coherent restrictions build on
these equations without exposing the underlying ringed-site maps.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {W X Y Z : Scheme.{u}}

namespace pushforwardComp

/-- The ambient pushforward composition comparisons satisfy associativity. -/
@[stacks 01LC "ambient module pushforward associativity"]
theorem associativity (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerRight (pushforwardComp f g) (pushforward h) ≪≫
        pushforwardComp (f ≫ g) h ≪≫
        pushforwardCongr (Category.assoc f g h) =
      Functor.associator (pushforward f) (pushforward g) (pushforward h) ≪≫
        Functor.isoWhiskerLeft (pushforward f) (pushforwardComp g h) ≪≫
        pushforwardComp f (g ≫ h) := sorry

/-- The ambient pushforward comparison satisfies the left identity law. -/
@[stacks 01LC "ambient module pushforward left identity"]
theorem left_unit (f : X ⟶ Y) :
    pushforwardComp (𝟙 X) f ≪≫
        pushforwardCongr (Category.id_comp f) =
      Functor.isoWhiskerRight (pushforwardId X) (pushforward f) ≪≫
        Functor.leftUnitor (pushforward f) := sorry

/-- The ambient pushforward comparison satisfies the right identity law. -/
@[stacks 01LC "ambient module pushforward right identity"]
theorem right_unit (f : X ⟶ Y) :
    pushforwardComp f (𝟙 Y) ≪≫
        pushforwardCongr (Category.comp_id f) =
      Functor.isoWhiskerLeft (pushforward f) (pushforwardId Y) ≪≫
        Functor.rightUnitor (pushforward f) := sorry

end pushforwardComp

end AlgebraicGeometry.Scheme.Modules
