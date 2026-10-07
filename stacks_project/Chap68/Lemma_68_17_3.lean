module

public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Source object properties imply relative morphism properties

If the source of a morphism of algebraic spaces is decent, reasonable, or has
property (β), then the morphism itself has the corresponding relative property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Decent

/-- Lemma 68.17.3 (1): if `X` is a decent algebraic space over a scheme `S`,
then any morphism `f : X ⟶ Y` of algebraic spaces over `S` is decent. -/
@[stacks 0ABX, instance 900]
instance of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsDecent X] : Decent f :=
  sorry

end Decent

namespace Reasonable

/-- Lemma 68.17.3 (2): if `X` is a reasonable algebraic space over a scheme
`S`, then any morphism `f : X ⟶ Y` of algebraic spaces over `S` is
reasonable. -/
@[stacks 0ABX, instance 900]
instance of_isReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsReasonable X] : Reasonable f :=
  sorry

end Reasonable

namespace PropertyBeta

/-- Lemma 68.17.3 (3): if `X` has property (β) of Lemma 68.5.1, then any
morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` has property (β). -/
@[stacks 0ABX, instance 900]
instance of_hasPropertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [HasPropertyBeta X] : PropertyBeta f :=
  sorry

end PropertyBeta

end AlgebraicGeometry.AlgebraicSpace
