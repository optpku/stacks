/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.InfinitesimalAutomorphisms
import StacksCheckRecall

/-!
# Tangent space and infinitesimal automorphisms of `Def_V`

The finite-projective deformation calculation is owned by the reusable
`ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective` API.
-/

@[expose] public section

open CategoryTheory
open Functor.Fiber
open scoped DualNumber

universe u

variable (Λ k V : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

namespace ArtinianLocalAlgCat.FiniteProjective

/- Lemma 93.4.3 -/
@[stacks 0DVQ] #check
  (ArtinianLocalAlgCat.FiniteProjective.eq_trivialTangent Λ k V :
    ∀ x : tangentSpace Λ k V, x = trivialTangent Λ k V)

#check
  (ArtinianLocalAlgCat.FiniteProjective.infAutOfEnd_bijective Λ k V :
    Function.Bijective (infAutOfEnd Λ k V))

#check
  (ArtinianLocalAlgCat.FiniteProjective.finiteDimensional_end k V :
    FiniteDimensional k (Module.End k V))

end ArtinianLocalAlgCat.FiniteProjective
