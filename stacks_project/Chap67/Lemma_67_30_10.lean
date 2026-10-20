module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport.Pullback
import StacksCheckRecall

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

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 67.30.10: The inverse image of a scheme-theoretic support of a
finite-type quasi-coherent module along a flat morphism of algebraic spaces
is the scheme-theoretic support of its pullback. -/
@[stacks 089C] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport.pullback_of_flat :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i],
      IsSchemeTheoreticSupport ((Modules.pullback f).obj F) (inverseImageι f i))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
      {f : Y ⟶ X} {i : Z ⟶ X} {pY : P ⟶ Y} {pZ : P ⟶ Z}
      (h : IsPullback pY pZ f i) [Flat f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType] [IsClosedImmersion i]
      [IsSchemeTheoreticSupport F i],
      IsSchemeTheoreticSupport ((Modules.pullback f).obj F) pY)
