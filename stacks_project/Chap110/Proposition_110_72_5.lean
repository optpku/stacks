module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import stacks_project.Chap55.Theorem_55_18_1_Model
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Example_100_12_5_Quotient
public import stacks_project.Chap110.Proposition_110_72_5_HomStack

/-!
# A non-algebraic Hom-stack

In the setup of Stacks 110.72, the Hom-stack of morphisms from a regular projective
flat family of geometrically connected curves into the classifying stack of fppf
torsors under a constant nonzero abelian scheme is not algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupScheme
open AlgebraicGeometry.GroupoidScheme
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.Hom
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- The spectrum of the formal power series ring `k⟦t⟧`. -/
def specPowerSeries (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (CommRingCat.of (PowerSeries k))

/-- Unfolding `specPowerSeries` recovers `Spec` of the power series ring. -/
theorem specPowerSeries_eq (k : Type u) [CommRing k] :
    specPowerSeries k = Spec (CommRingCat.of (PowerSeries k)) := sorry

/-- The constant abelian scheme `A = A₀ ×_{Spec k} Spec(k⟦t⟧)` associated to an
abelian variety `A₀` over `k`. -/
def constantAbelianScheme {k : Type u} [Field k] (A0 : SchemeOverField k) [GrpObj A0] :
    GroupScheme (specPowerSeries k) :=
  GroupScheme.baseChange (Grp.mk A0)
    (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))))

/-- The underlying object of `constantAbelianScheme A0` is the pullback of `A0`
along `Spec(k⟦t⟧) ⟶ Spec k`. -/
theorem constantAbelianScheme_X {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] :
    (constantAbelianScheme A0).X =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))))).obj A0 :=
  sorry

/-- The classifying stack `[S / A]` of a group scheme `A` over `S`, as the
quotient stack of the trivial action of `A` on `S`. This is the stack of fppf
`A`-torsors, pinned to `GroupoidsOver S`. -/
def classifyingTorsors {S : Scheme.{u}} (A : GroupScheme S) : GroupoidsOver S :=
  (ofGroupoidScheme (ofAction A (trivialAction A))).quotientStack

/-- `classifyingTorsors A` is the quotient stack of the trivial action of `A`. -/
theorem classifyingTorsors_eq {S : Scheme.{u}} (A : GroupScheme S) :
    classifyingTorsors A =
      (ofGroupoidScheme (ofAction A (trivialAction A))).quotientStack := sorry

/-- The special fibre of a scheme over `Spec(k⟦t⟧)`, obtained by pullback along
`Spec k ⟶ Spec(k⟦t⟧)` induced by the constant-coefficient map. -/
def specialFiber {k : Type u} [Field k] (X : Over (specPowerSeries k)) :
    SchemeOverField k :=
  (Over.pullback (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))).obj X

/-- Unfolding `specialFiber` recovers pullback along the constant-coefficient
morphism `Spec k ⟶ Spec(k⟦t⟧)`. -/
theorem specialFiber_eq {k : Type u} [Field k] (X : Over (specPowerSeries k)) :
    specialFiber X =
      (Over.pullback (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))).obj X :=
  sorry

/-- A field is an algebraic closure of a finite field. -/
def IsAlgebraicClosureOfFiniteField (k : Type u) [Field k] : Prop :=
  ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra F k), IsAlgClosure F k

/-- Unfolding `IsAlgebraicClosureOfFiniteField`. -/
theorem IsAlgebraicClosureOfFiniteField_iff (k : Type u) [Field k] :
    IsAlgebraicClosureOfFiniteField k ↔
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra F k), IsAlgClosure F k :=
  sorry

/-- An irreducible component of a scheme over a field, viewed as a scheme over `k`. -/
def irreducibleComponentOver {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)

/-- The structure morphism of `irreducibleComponentOver X Z` is the component
immersion followed by the structure morphism of `X`. -/
theorem irreducibleComponentOver_hom {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (irreducibleComponentOver X Z).hom =
      X.left.irreducibleComponentSubschemeι Z ≫ X.hom := sorry

/-- The cyclic successor on `Fin n`. -/
def cycleSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- Unfolding `cycleSucc`. -/
theorem cycleSucc_eq {n : ℕ} (hn : 0 < n) (i : Fin n) :
    cycleSucc hn i = ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ := sorry

/-- An at-worst-nodal curve over `k` with smooth irreducible components whose dual
graph contains a cycle of rational curves. The cycle need not include every
irreducible component, and components off the cycle need not be rational. -/
def IsNodalWithRationalComponentLoop {k : Type u} [Field k]
    (X : SchemeOverField k) : Prop :=
  SchemeOverField.atWorstNodal X ∧
    (∀ Z : irreducibleComponents X.left, Smooth (irreducibleComponentOver X Z).hom) ∧
    ∃ (n : ℕ) (hn : 0 < n) (C : Fin n → irreducibleComponents X.left)
      (node : Fin n → X.left),
      Function.Injective C ∧ Function.Injective node ∧
        (∀ i, Nonempty (RationalCurve k (irreducibleComponentOver X (C i)))) ∧
        (∀ i, node i ∈ (C i : Set X.left)) ∧
        (∀ i, node i ∈ (C (cycleSucc hn i) : Set X.left)) ∧
        (∀ i, SchemeOverField.isNode X (node i))

/-- Unfolding `IsNodalWithRationalComponentLoop`. -/
theorem IsNodalWithRationalComponentLoop_iff {k : Type u} [Field k]
    (X : SchemeOverField k) :
    IsNodalWithRationalComponentLoop X ↔
      SchemeOverField.atWorstNodal X ∧
        (∀ Z : irreducibleComponents X.left,
          Smooth (irreducibleComponentOver X Z).hom) ∧
        ∃ (n : ℕ) (hn : 0 < n) (C : Fin n → irreducibleComponents X.left)
          (node : Fin n → X.left),
          Function.Injective C ∧ Function.Injective node ∧
            (∀ i, Nonempty (RationalCurve k (irreducibleComponentOver X (C i)))) ∧
            (∀ i, node i ∈ (C i : Set X.left)) ∧
            (∀ i, node i ∈ (C (cycleSucc hn i) : Set X.left)) ∧
            (∀ i, SchemeOverField.isNode X (node i)) := sorry

/-- Proposition 110.72.5: let `k` be an algebraically closed field which is not
an algebraic closure of a finite field, let `A0` be a nonzero abelian variety
over `k`, and let `X` be a regular scheme, projective and flat over
`S = specPowerSeries k`, whose fibres are geometrically connected curves and
whose special fibre is an at-worst-nodal curve with smooth irreducible
components whose dual graph contains a cycle of rational curves. Then the
Hom-stack `homStack X (classifyingTorsors (constantAbelianScheme A0))` is not
an algebraic stack. -/
@[stacks 0AFC]
theorem not_isAlgebraic {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)) :
    ¬ AlgebraicStack (homStack X (classifyingTorsors (constantAbelianScheme A0))) :=
  sorry

end AlgebraicGeometry.HomStack
