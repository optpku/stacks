/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Differential

/-!
# Bijective differential condition for a formal object

Stacks Tag 06IM names the condition that the differential associated to a formal object of a
predeformation category is bijective on tangent spaces.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- 90.15.0.1: a formal object satisfies the condition that its differential maps derivations
of its complete local base bijectively to the tangent space of the predeformation category. -/
@[stacks 06IM] #check (FormalObject.BijectiveDifferential :
  (ξ : FormalObject p) → [Functor.IsPredeformationCategory p] → Prop)
