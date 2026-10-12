/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DualizingRank
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

/- Exercise 111.63.7 -/
@[stacks 0G19] #check (AlgebraicGeometry.SchemeOverField.dualizingModule_finiteLocallyFree_rank_eq_one :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Nonempty X.left] [IsProper X.hom] [HasExt (X.left.Modules)]
    (d : ℕ) (hd : topologicalKrullDim X.left = d) (ω : X.left.Modules)
    (t : Ext (𝟙_ (X.left.Modules)) ω d →ₗ[k] k)
    (h_pair : ∀ (i : ℕ) (hi : i ≤ d) (F : X.left.Modules) [F.IsCoherent],
      (tracePairing X t F hi).Nondegenerate)
    (h_neg : ∀ (i : ℕ) (F : X.left.Modules) [F.IsCoherent],
      d < i → Subsingleton (Ext F ω i))
    (r : ℕ) [IsFiniteLocallyFreeOfRank r ω], r = 1)
