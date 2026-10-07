module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
import StacksCheckRecall

/-!
# Composition of étale-local morphisms of algebraic spaces

If a scheme-morphism property that is étale local on source-and-target is stable
under composition, then so is its lift to morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 67.22.3: If a property `P` of morphisms of schemes is étale local on
source-and-target and stable under composition, then the class of morphisms of
algebraic spaces having property `P` is stable under composition. -/
@[stacks 0AML] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isStableUnderComposition :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderComposition],
      (etaleLocal P : MorphismProperty (AlgebraicSpace S)).IsStableUnderComposition)

/- The composition of morphisms of algebraic spaces having the lift of an
étale-local-on-source-and-target property `P` has that lift, when `P` is stable
under composition. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocal.comp :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} {g : Y ⟶ Z},
    etaleLocal P f → etaleLocal P g → etaleLocal P (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
