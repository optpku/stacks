/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.FiniteType
import StacksCheckRecall

@[expose] public section

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]

variable (φ : A →+* B) (hφ : Continuous φ)

/- Definition 87.29.1: let `A → B` be a continuous map of topological rings
(More on Algebra, Definition 15.36.1). We say `B` is topologically of finite type
over `A` if there exists an `A`-algebra map `MvPolynomial (Fin n) A →ₐ[A] B`
whose image is dense in `B`. -/
@[stacks 0ANS] #check
  (RingHom.topologicallyOfFiniteType_iff_denseRange φ hφ :
    φ.TopologicallyOfFiniteType ↔
      ∃ (n : ℕ) (g : MvPolynomial (Fin n) A →+* B),
        g.comp (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) = φ ∧ DenseRange g)
