/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Constructions
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Weak-ideal completion of an algebra

Given a topological ring `A` and an `A`-algebra `A'` without a topology, the weak-ideal
completion of `A'` is the inverse limit of `A' ⧸ I A'` over the weak ideals of definition
of `A`.
-/

@[expose] public section

noncomputable section

universe u

namespace TopologicalRing

variable (A A' : Type u) [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A']

/-- The transition map `A' ⧸ J A' →+* A' ⧸ I A'` of the inverse system, for `J ≤ I`. -/
def weakIdealTransition {I J : Ideal A} (hJI : J ≤ I) :
    A' ⧸ J.map (algebraMap A A') →+* A' ⧸ I.map (algebraMap A A') :=
  Ideal.Quotient.factor (Ideal.map_mono hJI)

/-- The completion `(A')^∧` of an `A`-algebra along the weak ideals of definition of `A`,
realized as compatible families in `Π I, A' ⧸ I A'`. -/
def weakIdealCompletion : Type u :=
  { f : ∀ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      A' ⧸ I.1.map (algebraMap A A') //
    ∀ {I J : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I}} (hJI : J.1 ≤ I.1),
      weakIdealTransition A A' hJI (f J) = f I }

namespace weakIdealCompletion

/-- Zero is the zero family of residue classes. -/
instance instZero : Zero (weakIdealCompletion A A') where
  zero := ⟨0, sorry⟩

/-- Pointwise addition of compatible families. -/
instance instAdd : Add (weakIdealCompletion A A') where
  add x y := ⟨x.val + y.val, sorry⟩

/-- Pointwise negation of compatible families. -/
instance instNeg : Neg (weakIdealCompletion A A') where
  neg x := ⟨-x.val, sorry⟩

/-- Pointwise subtraction of compatible families. -/
instance instSub : Sub (weakIdealCompletion A A') where
  sub x y := ⟨x.val - y.val, sorry⟩

/-- Natural-number scalar multiplication on compatible families. -/
instance instNSmul : SMul ℕ (weakIdealCompletion A A') where
  smul n x := ⟨n • x.val, sorry⟩

/-- Integer scalar multiplication on compatible families. -/
instance instZSmul : SMul ℤ (weakIdealCompletion A A') where
  smul n x := ⟨n • x.val, sorry⟩

/-- One is the unit family of residue classes. -/
instance instOne : One (weakIdealCompletion A A') where
  one := ⟨1, sorry⟩

/-- Pointwise multiplication of compatible families. -/
instance instMul : Mul (weakIdealCompletion A A') where
  mul x y := ⟨x.val * y.val, sorry⟩

/-- Pointwise natural-number powers of compatible families. -/
instance instPow : Pow (weakIdealCompletion A A') ℕ where
  pow x n := ⟨x.val ^ n, sorry⟩

/-- Natural-number cast of compatible families. -/
instance instNatCast : NatCast (weakIdealCompletion A A') where
  natCast n := ⟨n, sorry⟩

/-- Integer cast of compatible families. -/
instance instIntCast : IntCast (weakIdealCompletion A A') where
  intCast n := ⟨n, sorry⟩

/-- The weak-ideal completion is a commutative ring under pointwise operations. -/
instance instCommRing : CommRing (weakIdealCompletion A A') :=
  Subtype.val_injective.commRing (fun x : weakIdealCompletion A A' => x.val)
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The inverse-limit topology, induced from the product of discrete topologies on the
stage quotients `A' ⧸ I A'`. -/
instance instTopologicalSpace : TopologicalSpace (weakIdealCompletion A A') :=
  TopologicalSpace.induced Subtype.val <|
    ⨅ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace.induced (fun f => f I)
        (⊥ : TopologicalSpace (A' ⧸ I.1.map (algebraMap A A')))

/-- Canonical map from `A'` into the inverse-limit completion. -/
def of : A' →+* weakIdealCompletion A A' where
  toFun x := ⟨fun _ => Ideal.Quotient.mk _ x, fun _ => rfl⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Projection from the completion onto the stage quotient `A' ⧸ I A'`. -/
def eval {I : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I) :
    weakIdealCompletion A A' →+* A' ⧸ I.map (algebraMap A A') where
  toFun x := x.val ⟨I, hI⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Families in the completion are compatible with the inverse-system transitions. -/
theorem val_compat (x : weakIdealCompletion A A')
    {I J : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I)
    (hJ : Ideal.IsWeakIdealOfDefinition J) (hJI : J ≤ I) :
    weakIdealTransition A A' hJI (eval A A' hJ x) = eval A A' hI x := sorry

/-- Equality of completions is equality of all stage projections. -/
theorem ext {x y : weakIdealCompletion A A'}
    (h : ∀ (I : Ideal A) (hI : Ideal.IsWeakIdealOfDefinition I),
      eval A A' hI x = eval A A' hI y) : x = y := sorry

/-- Stage projection of the canonical map `A' → (A')^∧` is the quotient map. -/
theorem eval_of {I : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I) (x : A') :
    eval A A' hI (of A A' x) = Ideal.Quotient.mk _ x := sorry

/-- The completion is an `A'`-algebra via `weakIdealCompletion.of`. -/
instance instAlgebra : Algebra A' (weakIdealCompletion A A') := (of A A').toAlgebra

/-- The completion is an `A`-algebra via `A → A' → (A')^∧`, the horizontal arrow of the
localization square. -/
instance instAlgebraBase : Algebra A (weakIdealCompletion A A') :=
  ((of A A').comp (algebraMap A A')).toAlgebra

/-- The `A`-algebra structure on the completion factors through `A'`. -/
instance instIsScalarTower : IsScalarTower A A' (weakIdealCompletion A A') := sorry

/-- The algebra map `A → (A')^∧` is the composition of `algebraMap A A'` with
`weakIdealCompletion.of`. -/
theorem algebraMap_eq :
    algebraMap A (weakIdealCompletion A A') = (of A A').comp (algebraMap A A') := sorry

/-- Addition and multiplication are continuous on the inverse-limit topology. -/
instance instIsTopologicalRing : IsTopologicalRing (weakIdealCompletion A A') := sorry

end weakIdealCompletion

end TopologicalRing
