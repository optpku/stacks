module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Map

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

/-- Direct image of commutative-ring sheaves respects composition. -/
noncomputable abbrev commRingPushforwardCompIso {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    commRingPushforward f ⋙ commRingPushforward g ≅ commRingPushforward (f ≫ g) :=
  AlgebraicSpace.commRingPushforwardComp f g

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}} {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.map sq :
  ConormalAlgebra.pullback f i' ⟶ ConormalAlgebra.total i)
