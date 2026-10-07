module

public import ReasLib.RingTheory.DirectLimit.Comparison
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local rings and directed ring colimits

This leaf records the local-ring API of a directed colimit of commutative
rings.  The local-ring structure and the locality of the canonical stage maps
are canonical.  Maps into another ring are handled through the universal
property without requiring the target or the direct limit to carry a chosen
local-ring structure.

@stack 00QV
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

variable {I : Type u} [Preorder I]
variable (R : I → Type v) [∀ i, CommRing (R i)]
variable (rho : ∀ i j, i ≤ j → R i →+* R j)

section LocalSystem

variable [Nonempty I] [IsDirectedOrder I]
variable [DirectedSystem R (fun i j h ↦ rho i j h)]
variable [∀ i, IsLocalRing (R i)] [∀ i j h, IsLocalHom (rho i j h)]

/-- The canonical local-ring structure on a directed colimit of local rings. -/
@[stacks 00QV "local directed colimit"]
instance colimitLocalRing :
    IsLocalRing (Ring.DirectLimit R (fun i j h ↦ rho i j h)) := sorry

end LocalSystem

section StageMap

variable [IsDirectedOrder I]
variable [DirectedSystem R (fun i j h ↦ rho i j h)]
variable [∀ i j h, IsLocalHom (rho i j h)]

/-- Locality of the canonical map from a stage to a directed colimit is
available to typeclass search. -/
@[stacks 00QV "local directed-colimit stage map"]
instance ofLocal (i : I) :
    IsLocalHom (Ring.DirectLimit.of R (fun i j h ↦ rho i j h) i) := sorry

end StageMap

section LiftCompatibility

variable {T : Type w} [CommRing T]
variable (g : ∀ i, R i →+* T)

/-- A family of maps compatible as ring homomorphisms is compatible in the
pointwise form expected by `Ring.DirectLimit.lift`. -/
theorem lift_compatible_of_comp
    (hcomp : ∀ i j (h : i ≤ j), (g j).comp (rho i j h) = g i) :
    ∀ i j (h : i ≤ j) (x : R i), g j (rho i j h x) = g i x := sorry

end LiftCompatibility

section Lift

variable [Nonempty I] [IsDirectedOrder I]
variable {T : Type w} [CommRing T]
variable (g : ∀ i, R i →+* T)

/-- If every map in a compatible family out of the stages reflects units, then
the induced map out of the directed colimit reflects units.  No local-ring
structure on either the stages or the target is needed. -/
@[stacks 00QV "local direct-limit lift"]
theorem lift_isLocalHom
    (hcompat : ∀ i j (h : i ≤ j) (x : R i), g j (rho i j h x) = g i x)
    [∀ i, IsLocalHom (g i)] :
    IsLocalHom (Ring.DirectLimit.lift R (fun i j h ↦ rho i j h) T g hcompat) := sorry

/-- Locality of a direct-limit lift, with compatibility supplied as an
equality of ring homomorphisms. -/
@[stacks 00QV "local direct-limit lift"]
theorem lift_isLocalHom_of_comp
    (hcomp : ∀ i j (h : i ≤ j), (g j).comp (rho i j h) = g i)
    [∀ i, IsLocalHom (g i)] :
    IsLocalHom
      (Ring.DirectLimit.lift R (fun i j h ↦ rho i j h) T g
        (lift_compatible_of_comp R rho g hcomp)) := sorry

end Lift

/-- Locality of chosen stage maps is available to typeclass search without
installing any choice-dependent algebra structure. -/
@[stacks 00QV "local direct-limit comparison"]
instance toLimitHom_isLocalHom
    {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ rho i j h) ≃+* T) (i : I)
    [IsLocalHom (Ring.DirectLimit.of R (fun i j h ↦ rho i j h) i)] :
    IsLocalHom (toLimitHom R rho e i) := sorry

end Ring.DirectLimit
