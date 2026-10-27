/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.Proper
import StacksCheckRecall

/-!
# Finite-dimensionality of Inf and T for proper morphisms of schemes over a field

In Lemma 93.10.3, if `X` and `Y` are both proper over `k`, then `Inf(Def_{X ⟶ Y})`
and `T Def_{X ⟶ Y}` are finite-dimensional `k`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FlatSchemeMorphismCat

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)
variable [IsProper hX] [IsProper hY]

/- Lemma 93.10.4 (1)
In Lemma 93.10.3, if `X` and `Y` are both proper over `k`, then `Inf(Def_{X ⟶ Y})`
is a finite-dimensional `k`-vector space. -/
@[stacks 0E3W] #check (FlatSchemeMorphismCat.instFiniteDimensional_inf Λ k f hX hY hf :
  FiniteDimensional k (FlatSchemeMorphismCat.inf Λ k f hX hY hf))

/- Lemma 93.10.4 (2)
In Lemma 93.10.3, if `X` and `Y` are both proper over `k`, then `T Def_{X ⟶ Y}`
is a finite-dimensional `k`-vector space. -/
@[stacks 0E3W] #check (FlatSchemeMorphismCat.instFiniteDimensional_tangentSpace Λ k f hX hY hf :
  FiniteDimensional k (FlatSchemeMorphismCat.tangentSpace Λ k f hX hY hf))

end FlatSchemeMorphismCat
