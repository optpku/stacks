/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Compactification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Compactification along elementary distinguished squares

Compactifications of the two legs of a dense elementary distinguished square
over a finite-type base yield a compactification of its vertex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasCompactification

/-- If the legs of a dense elementary distinguished square are compactifiable
over a finite-type base, then its vertex is compactifiable over that base. -/
@[stacks 0F4B]
theorem of_isElementaryDistinguishedSquare
    {B U U1 U2 : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    [FiniteType (SchemeRealization.toBase B)] (fU : U ⟶ B) [FiniteType fU] [Separated fU]
    (j : U2 ⟶ U) (f : U1 ⟶ U) [IsElementaryDistinguishedSquare j f]
    [HasCompactification (j ≫ fU)] [HasCompactification (f ≫ fU)]
    (h_dense : Dense (Set.range (Points.map (pullback.fst j f ≫ j)))) :
    HasCompactification fU :=
  sorry

end HasCompactification

end AlgebraicGeometry.AlgebraicSpace
