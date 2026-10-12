/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small

/- Definition 59.20.2: The big standard sites over a scheme, and the small
Zariski and étale sites with their inherited topologies and inclusions into the
corresponding big sites. -/
@[stacks 03XB] #check (AlgebraicGeometry.StandardTopology.overTopology :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme),
    CategoryTheory.GrothendieckTopology (CategoryTheory.Over S))

@[stacks 03XB] #check (AlgebraicGeometry.SmallStandardTopology.site :
  ∀ (σ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme),
    CategoryTheory.Cat)

@[stacks 03XB] #check (AlgebraicGeometry.SmallStandardTopology.topology :
  ∀ (σ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme),
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.SmallStandardTopology.site σ S))

@[stacks 03XB] #check (AlgebraicGeometry.SmallStandardTopology.toOver :
  ∀ (σ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme),
    CategoryTheory.Functor (AlgebraicGeometry.SmallStandardTopology.site σ S)
      (CategoryTheory.Over S))
