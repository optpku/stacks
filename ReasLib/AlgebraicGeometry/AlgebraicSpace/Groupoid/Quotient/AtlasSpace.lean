module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small

/-!
# Atlas morphisms of presented quotient stacks

A presentation of a quotient stack by an algebraic space recovers its atlas as a
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The morphism from the object space to an algebraic space presenting the quotient
stack, recovered from the canonical quotient atlas. -/
def atlasSpace {S : Scheme.{u}} {Y : AlgebraicSpace S} (G : GroupoidAlgebraicSpace Y)
    {X : AlgebraicSpace S} (e : SmallQuotient.quotientStack G ≌ X.toGroupoids) :
    G.U.left ⟶ X :=
  AlgebraicSpace.toGroupoids.recover (Bicategory.Equivalence.id _) e (SmallQuotient.atlas G)

/-- The atlas morphism is the recovery of the canonical quotient atlas through the
identity presentation of the object space and the given quotient presentation. -/
theorem atlasSpace_spec {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace Y) {X : AlgebraicSpace S}
    (e : SmallQuotient.quotientStack G ≌ X.toGroupoids) :
    atlasSpace G e =
      AlgebraicSpace.toGroupoids.recover (Bicategory.Equivalence.id _) e
        (SmallQuotient.atlas G) :=
  rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace
