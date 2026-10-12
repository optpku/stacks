/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism.ProperIntersection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open ProjectiveSpace.VectorSpace
open ProjectiveEndomorphism

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Nontrivial V]

/- Lemma 43.23.8: if the closed subvarieties `X` and `Y` of `ℙ(V)` intersect
properly, `X ≠ ℙ(V)`, and `X ∩ Y` is nonempty, then a nonempty open subset of
`ℙ((End(V))∨)` has its closed points swept out by lines through `[id_V]` on which
every `[g]` is defined along `X` and the closed image `g(X)` intersects `Y`
properly. Membership of `[g]` in a quotient-defined line is expressed by
factorization of evaluation through the line quotient. -/
@[stacks 0B1S] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism.exists_open_coveredBy_lines_endomorphism_image_intersectsProperly :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [Nontrivial V]
      (X Y : IrreducibleCloseds (scheme k V))
      (hproper : Closeds.IntersectProperly (Closeds.closure (X : Set _))
        (Closeds.closure (Y : Set (scheme k V))))
      (hX : (X : Set (scheme k V)) ≠ Set.univ)
      (hXY : ((X : Set (scheme k V)) ∩ (Y : Set (scheme k V))).Nonempty),
      ∃ U : (scheme k (Module.Dual k (Module.End k V))).Opens, Nonempty U ∧
        ∀ q : scheme k (Module.Dual k (Module.End k V)),
          IsClosed ({q} : Set (scheme k (Module.Dual k (Module.End k V)))) → q ∈ U →
          ∃ ℓ : ProjectiveSpace.VectorSpace.Line k
              (Module.Dual k (Module.End k V)),
            q ∈ ℓ.carrier ∧
              LinearMap.ker ℓ.quotient ≤
                LinearMap.ker (Module.Dual.eval k (Module.End k V) 1) ∧
              ∀ (g : Module.End k V) (hg : g ≠ 0),
                LinearMap.ker ℓ.quotient ≤
                    LinearMap.ker (Module.Dual.eval k (Module.End k V) g) →
                  (X : Set (scheme k V)) ⊆
                      (ProjectiveEndomorphism.domain (Projectivization.mk k g hg) : Set _) ∧
                    Closeds.IntersectProperly
                      (ProjectiveEndomorphism.image (Projectivization.mk k g hg) (X : Set _))
                        (Closeds.closure (Y : Set (scheme k V))))
