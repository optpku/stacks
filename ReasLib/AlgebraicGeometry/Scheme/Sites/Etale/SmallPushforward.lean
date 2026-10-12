/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyB
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- A morphism of schemes with Property (B) has a small étale pushforward that
preserves locally surjective morphisms of sheaves. -/
theorem smallMorphism_pushforward_preservesLocallySurjective_of_hasPropertyB
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    (hB : hasPropertyB f) :
    (smallMorphism f).pushforward.PreservesLocallySurjective := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
