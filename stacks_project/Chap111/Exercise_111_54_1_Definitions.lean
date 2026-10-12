/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReasLib.RingTheory.LocalRing.LocalSubring
public import Mathlib.Topology.KrullDimension
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

section Domination

variable {K : Type u} [Field K] (A B : LocalSubring K)

/- Exercise 111.54.1 (Definitions): for local rings `A` and `B` in a common field,
`A` dominates `B` means `B ≤ A`: `B` is contained in `A` and the maximal ideal of
`A` contracts to the maximal ideal of `B`. The companion checks below give the
other four definitions requested in the exercise. -/
@[stacks 06A0]
#check (LocalSubring.le_iff_maximalIdeal_comap B A :
  B ≤ A ↔ ∃ h : B.toSubring ≤ A.toSubring,
    (IsLocalRing.maximalIdeal A.toSubring).comap (Subring.inclusion h) =
      IsLocalRing.maximalIdeal B.toSubring)

/- Equivalently, the inclusion of `B` into `A` is a local ring homomorphism. -/
#check (LocalSubring.le_def :
  B ≤ A ↔ ∃ h : B.toSubring ≤ A.toSubring, IsLocalHom (Subring.inclusion h))

end Domination

section Schemes

variable (X Z : Scheme.{u}) (f : X ⟶ Z) (Y : TopologicalSpace.IrreducibleCloseds X)

/- A scheme is separated when its morphism to the terminal scheme is separated. -/
#check (Scheme.IsSeparated X : Prop)

/- A morphism is separated when its diagonal is a closed immersion. -/
#check (IsSeparated f : Prop)

/- Absolute separatedness agrees with separatedness of the terminal morphism. -/
#check (Scheme.isSeparated_iff X : X.IsSeparated ↔ IsSeparated (terminal.from X))

/- A morphism is universally closed when every base change is a closed map. -/
#check (UniversallyClosed f : Prop)

/- Universal closedness is the universally quantified topological closed-map property. -/
#check (universallyClosed_iff f :
  UniversallyClosed f ↔
    MorphismProperty.universally (topologically IsClosedMap) f)

/- The dimension of a scheme is the topological Krull dimension of its underlying space. -/
#check (topologicalKrullDim X : WithBot ℕ∞)

/- The codimension of an irreducible closed subscheme is the coheight of its support. -/
#check (Order.coheight Y : ℕ∞)

end Schemes
