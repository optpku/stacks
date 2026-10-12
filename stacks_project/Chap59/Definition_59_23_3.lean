/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Definition 59.23.3: For a scheme `S`, the structure sheaf is the sheaf of rings
`𝒪_S` on the small Zariski site, the small étale site, or the big standard `τ`-site. -/
@[stacks 04HS] #check (AlgebraicGeometry.Scheme.Zariski.Small.structureSheaf :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    Sheaf S.smallZariskiTopology RingCat.{u})

@[stacks 04HS] #check (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    Sheaf S.smallEtaleTopology RingCat.{u})

@[stacks 04HS] #check (AlgebraicGeometry.StandardTopology.Big.structureSheaf :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
    Sheaf (τ.overTopology S) RingCat.{u})
