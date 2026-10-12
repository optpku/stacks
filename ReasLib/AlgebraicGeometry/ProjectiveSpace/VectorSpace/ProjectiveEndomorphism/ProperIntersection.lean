/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism.Map
public import ReasLib.Topology.KrullDimension.ProperIntersection

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open ProjectiveSpace.VectorSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Nontrivial V]

/-- If two closed subvarieties intersect properly and one is proper, a general projective
endomorphism image intersects the other properly along a line through the identity. -/
theorem exists_open_coveredBy_lines_endomorphism_image_intersectsProperly
    (X Y : IrreducibleCloseds (scheme k V))
    (hproper : Closeds.IntersectProperly (Closeds.closure (X : Set _))
      (Closeds.closure (Y : Set (scheme k V))))
    (hX : (X : Set (scheme k V)) ≠ Set.univ)
    (hXY : ((X : Set (scheme k V)) ∩ (Y : Set (scheme k V))).Nonempty) :
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
                    (domain (Projectivization.mk k g hg) : Set _) ∧
                  Closeds.IntersectProperly
                    (image (Projectivization.mk k g hg) (X : Set _))
                      (Closeds.closure (Y : Set (scheme k V))) := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism
