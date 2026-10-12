/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra
public import ReasLib.RingTheory.DirectLimit.Constant
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct limits of algebras over a fixed base

This leaf equips a directed system of commutative `R`-algebras with its
canonical `R`-algebra direct limit.  It exposes the stage inclusions and the
universal property directly as `AlgHom`s, so downstream users do not need to
rebuild scalar compatibility from the underlying ring direct limit.
-/

@[expose] public section

universe u v w z

noncomputable section

namespace Ring.DirectLimit

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I]
variable (S : I → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
variable (φ : ∀ i j, i ≤ j → S i →ₐ[R] S j)

/-- Forgetting the algebra-hom structure of a directed system gives the
corresponding directed system of linear maps over the fixed base. -/
@[stacks 05LI "linear directed system"]
instance linearDirectedSystem [DirectedSystem S (fun i j h ↦ (φ i j h : S i →+* S j))] :
    DirectedSystem S (fun i j h ↦ (φ i j h).toLinearMap) where
  map_self := sorry
  map_map := sorry

/-- The canonical map from the fixed base ring to the direct limit of a
directed system of `R`-algebras. -/
@[stacks 031N "direct-limit algebra structure"]
noncomputable def algebraMap [IsDirectedOrder I] :
    R →+* Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j)) :=
  let Rconst : I → Type u := fun _ ↦ R
  let ιR : ∀ i j : I, i ≤ j → Rconst i → Rconst j :=
    fun _ _ _ ↦ RingHom.id R
  let fromConst : Ring.DirectLimit Rconst ιR →+*
      Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j)) :=
    Ring.DirectLimit.lift Rconst ιR
      (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j)))
      (fun i ↦ (Ring.DirectLimit.of S (fun i j h ↦ (φ i j h : S i →+* S j)) i).comp
        (_root_.Algebra.algebraMap R (S i)))
      sorry
  let constEquiv : Ring.DirectLimit Rconst ιR ≃+* R :=
    Ring.DirectLimit.constantEquiv R I
  fromConst.comp constEquiv.symm.toRingHom

/-- A directed system of commutative `R`-algebras induces the canonical
`R`-algebra structure on its direct limit. -/
@[stacks 031N "direct-limit algebra structure"]
noncomputable instance algebra [IsDirectedOrder I] :
    Algebra R (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j))) :=
  (Ring.DirectLimit.algebraMap S φ).toAlgebra

/-- The direct-limit algebra map can be computed using the structural map at
any stage. -/
@[stacks 031N "direct-limit algebra structure"]
theorem algebraMap_eq_of [IsDirectedOrder I] (i : I) (r : R) :
    _root_.Algebra.algebraMap R
        (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j))) r =
      Ring.DirectLimit.of S (fun i j h ↦ (φ i j h : S i →+* S j)) i
        (_root_.Algebra.algebraMap R (S i) r) := sorry

/-- The structural map from a stage into the direct limit preserves the
fixed base-ring action. -/
@[stacks 031N "direct-limit algebra structure"]
theorem ofAlgHom_commutes [IsDirectedOrder I] (i : I) (r : R) :
    Ring.DirectLimit.of S (fun i j h ↦ (φ i j h : S i →+* S j)) i
        (_root_.Algebra.algebraMap R (S i) r) =
      _root_.Algebra.algebraMap R
        (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j))) r := sorry

/-- The canonical map from a stage of the system into the direct limit,
viewed as an `R`-algebra homomorphism. -/
@[stacks 031N "direct-limit algebra structure"]
noncomputable def ofAlgHom [IsDirectedOrder I] (i : I) :
    S i →ₐ[R] Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j)) :=
  { toRingHom := Ring.DirectLimit.of S (fun i j h ↦ (φ i j h : S i →+* S j)) i
    commutes' := ofAlgHom_commutes S φ i }

/-- The algebra-hom stage inclusion evaluates through the underlying direct-limit
stage map. -/
@[simp, stacks 031N "direct-limit algebra structure"]
theorem ofAlgHom_apply [IsDirectedOrder I] (i : I) (x : S i) :
    ofAlgHom S φ i x =
      Ring.DirectLimit.of S (fun i j h ↦ (φ i j h : S i →+* S j)) i x := sorry

/-- The canonical fixed-base algebra structure on the direct limit and the
algebra structure induced by a stage form a scalar tower. -/
@[stacks 031N "direct-limit stage algebra"]
theorem stageAlgebra_isScalarTower [IsDirectedOrder I] (i : I) :
    -- Local instance justification (stage-indexed, not globally registered): `i` selects this action.
    letI : Algebra (S i) (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j))) :=
      Ring.DirectLimit.Algebra.stageAlgebra (fun i j h ↦ (φ i j h).toRingHom) i
    IsScalarTower R (S i) (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j))) := sorry

/-- The algebra-hom stage inclusions respect the transition maps. -/
@[stacks 031N "direct-limit algebra structure"]
theorem ofAlgHom_comp_transition [IsDirectedOrder I] {i j : I} (hij : i ≤ j) :
    (ofAlgHom S φ j).comp (φ i j hij) = ofAlgHom S φ i := sorry

/-- The algebra-hom stage inclusions commute pointwise with transitions. -/
@[simp, stacks 031N "direct-limit algebra structure"]
theorem ofAlgHom_comp_transition_apply [IsDirectedOrder I]
    {i j : I} (hij : i ≤ j) (x : S i) :
    ofAlgHom S φ j (φ i j hij x) = ofAlgHom S φ i x := sorry

/-- The universal ring-hom lift of compatible algebra-hom stage maps preserves
the `R`-algebra structure. -/
@[stacks 031N "direct-limit algebra structure"]
theorem liftAlgHom_commutes [IsDirectedOrder I] {A : Type z} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i)
    (r : R) :
    Ring.DirectLimit.lift S (fun i j h ↦ (φ i j h : S i →+* S j)) A (fun i ↦ (g i).toRingHom)
        (fun i j hij x ↦ DFunLike.congr_fun (hg i j hij) x)
        (_root_.Algebra.algebraMap R
          (Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j))) r) =
      _root_.Algebra.algebraMap R A r := sorry

/-- Compatible stage algebra maps assemble to a canonical algebra homomorphism
out of the direct limit. -/
@[stacks 031N "direct-limit algebra structure"]
noncomputable def liftAlgHom [IsDirectedOrder I] {A : Type z} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i) :
    Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j)) →ₐ[R] A :=
  { toRingHom :=
      Ring.DirectLimit.lift S (fun i j h ↦ (φ i j h : S i →+* S j)) A (fun i ↦ (g i).toRingHom)
        (fun i j hij x ↦ DFunLike.congr_fun (hg i j hij) x)
    commutes' := liftAlgHom_commutes S φ g hg }

/-- The universal algebra-hom lift restricts to the specified stage map. -/
@[stacks 031N "direct-limit algebra structure"]
theorem liftAlgHom_of [IsDirectedOrder I] {A : Type z} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i)
    (i : I) :
    (liftAlgHom S φ g hg).comp (ofAlgHom S φ i) = g i := sorry

/-- The universal algebra-hom lift evaluates on a stage generator through the
specified stage map. -/
@[simp, stacks 031N "direct-limit algebra structure"]
theorem liftAlgHom_of_apply [IsDirectedOrder I] {A : Type z} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i)
    (i : I) (x : S i) :
    liftAlgHom S φ g hg (ofAlgHom S φ i x) = g i x := sorry

/-- Algebra homomorphisms out of the direct limit are determined by their
restrictions to all stages. -/
@[stacks 031N "direct-limit algebra structure"]
theorem algHom_ext [IsDirectedOrder I] {A : Type z} [CommRing A] [Algebra R A]
    {f g : Ring.DirectLimit S (fun i j h ↦ (φ i j h : S i →+* S j)) →ₐ[R] A}
    (h : ∀ i, f.comp (ofAlgHom S φ i) = g.comp (ofAlgHom S φ i)) :
    f = g := sorry

end Ring.DirectLimit
