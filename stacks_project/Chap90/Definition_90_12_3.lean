/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
import StacksCheckRecall

/-!
# Differential of a morphism of predeformation categories
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]

/- Definition 90.12.3: let `φ : ℱ ⟶ 𝒢` be a morphism of predeformation categories. -/
@[stacks 06II] #check (CategoryTheory.BasedFunctor.differential :
  (BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) →
    Functor.tangentSpace p → Functor.tangentSpace q)
