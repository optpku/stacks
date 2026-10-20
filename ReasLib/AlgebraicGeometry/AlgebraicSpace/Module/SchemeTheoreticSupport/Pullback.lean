module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat inverse images of scheme-theoretic supports

The inverse image of a scheme-theoretic support of a finite-type quasi-coherent
module along a flat morphism of algebraic spaces is again a scheme-theoretic
support.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace IsSchemeTheoreticSupport

/-- The inverse image of a scheme-theoretic support of a finite-type
quasi-coherent module along a flat morphism of algebraic spaces is a
scheme-theoretic support of the pulled-back module. -/
@[stacks 089C]
instance pullback_of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i] :
    IsSchemeTheoreticSupport ((pullback f).obj F) (inverseImageι f i) :=
  sorry

/-- Scheme-theoretic support of a finite-type quasi-coherent module is preserved
by pullback along a flat morphism of algebraic spaces, as a statement about
chosen pullbacks. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : Y ⟶ X} {i : Z ⟶ X} {pY : P ⟶ Y} {pZ : P ⟶ Z}
    (h : IsPullback pY pZ f i) [Flat f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [IsClosedImmersion i]
    [IsSchemeTheoreticSupport F i] :
    IsSchemeTheoreticSupport ((pullback f).obj F) pY :=
  sorry

end IsSchemeTheoreticSupport

end AlgebraicGeometry.AlgebraicSpace.Modules
