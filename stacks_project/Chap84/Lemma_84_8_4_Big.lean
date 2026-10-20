module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos

/-! # Compatibility check for the canonical big étale morphism of topoi -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (Y ⟶ X) → MorphismOfTopoiIn (overEtaleTopology X) (overEtaleTopology Y))
