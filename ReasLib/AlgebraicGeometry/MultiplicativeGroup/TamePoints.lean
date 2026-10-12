/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameFiber
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Group.Conj

/-! Actual positive-degree closed points and geometric Frobenius on their tame fibers. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
noncomputable section
universe u

namespace MultiplicativeGroupTame
variable (k : Type u) [Field k]

def overField : SchemeOverField k := Over.mk (structureMap k)

instance locallyOfFiniteType : LocallyOfFiniteType (overField k).hom := by
  sorry

/-- These are the actual closed points, indexed by their residue-field degree. -/
def points (d : ℕ+) :=
  {x : closedPoints (overField k).left // (overField k).hom.residueDegree x.val = d.val}

instance points_finite [Finite k] (d : ℕ+) : Finite (points k d) := by
  sorry

/-- The canonical geometric point at x comes from its own residue field. -/
def pointOver (x : closedPoints (overField k).left) : GeometricPoint (space k) :=
  GeometricPoint.of (AlgebraicClosure ((space k).residueField x.val))
    (Spec.map (CommRingCat.ofHom
      (algebraMap ((space k).residueField x.val)
        (AlgebraicClosure ((space k).residueField x.val)))) ≫
      (space k).fromSpecResidueField x.val)

/-- Precompose lifts with a specified automorphism of their actual source spectrum. -/
def pointAut {X : Scheme.{u}} (s : GeometricPoint X)
    (τ : Spec (.of s.K) ≅ Spec (.of s.K)) (hτ : τ.hom ≫ s.hom = s.hom) :
    Aut s.finiteFiber :=
  NatIso.ofComponents (fun V : Scheme.FiniteEtale X ↦
    { hom := FintypeCat.homMk (fun (a : Over.mk s.hom ⟶ Over.mk V.hom) ↦
        Over.homMk (τ.hom ≫ a.left)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f ↦ τ.hom ≫ f) a.w).trans hτ)))
      inv := FintypeCat.homMk (fun (a : Over.mk s.hom ⟶ Over.mk V.hom) ↦
        Over.homMk (τ.inv ≫ a.left) (by
          have hi : τ.inv ≫ s.hom = s.hom := by
            calc
              τ.inv ≫ s.hom = τ.inv ≫ τ.hom ≫ s.hom := congrArg (τ.inv ≫ ·) hτ.symm
              _ = s.hom := τ.inv_hom_id_assoc _
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun f ↦ τ.inv ≫ f) a.w).trans hi)))
      hom_inv_id := by sorry
      inv_hom_id := by sorry }) (fun _ ↦ by sorry)

theorem pointAut_apply {X : Scheme.{u}} (s : GeometricPoint X)
    (τ : Spec (.of s.K) ≅ Spec (.of s.K)) (hτ : τ.hom ≫ s.hom = s.hom)
    (V : Scheme.FiniteEtale X) (a : s.finiteFiber.obj V) :
    ((pointAut s τ hτ).hom.app V a).left = τ.hom ≫ a.left := rfl

variable [Finite k]

/-- Inverse of the actual #κ(x)-power automorphism, not an arbitrary degree-d element. -/
def residueGeometric (x : closedPoints (overField k).left) :
    (AlgebraicClosure ((space k).residueField x.val)) ≃ₐ[(space k).residueField x.val]
      AlgebraicClosure ((space k).residueField x.val) :=
  -- Local instance justification (proof-local temporary data): Closedness over the finite base makes this particular residue field finite.
  letI : Finite ((space k).residueField x.val) :=
    SchemeOverField.closedPointResidueFieldFinite (overField k) x
  -- Local instance justification (noncanonical choice): Frobenius needs a finite enumeration of this residue field; its canonical power map is enumeration-independent.
  letI : Fintype ((space k).residueField x.val) := Fintype.ofFinite _
  (FiniteField.frobeniusAlgEquivOfAlgebraic ((space k).residueField x.val)
    (AlgebraicClosure ((space k).residueField x.val)))⁻¹

def residueSpecIso (x : closedPoints (overField k).left) :
    Spec (.of (pointOver k x).K) ≅ Spec (.of (pointOver k x).K) :=
  Scheme.Spec.mapIso (residueGeometric k x).toRingEquiv.toCommRingCatIso.op

theorem residueSpecIso_over (x : closedPoints (overField k).left) :
    (residueSpecIso k x).hom ≫ (pointOver k x).hom = (pointOver k x).hom := by
  sorry

/-- The actual ordinary local Frobenius, before projection to tame covers. -/
def ordinaryLocalFrobenius (x : closedPoints (overField k).left) :
    Aut (pointOver k x).finiteFiber :=
  pointAut (pointOver k x) (residueSpecIso k x) (residueSpecIso_over k x)

/-- The local tame Frobenius is the canonical restriction of the preceding action. -/
def localFrobenius (x : closedPoints (overField k).left) :
    fundamentalGroup k (pointOver k x) :=
  quotientMap k (pointOver k x) (ordinaryLocalFrobenius k x)

theorem localFrobenius_apply (x : closedPoints (overField k).left)
    (V : Cover k) (a : (fiber k (pointOver k x)).obj V) :
    ((localFrobenius k x).hom.app V a).left = (residueSpecIso k x).hom ≫ a.left := rfl

/-- A supplied fiber path transports the concrete action; none is selected from existence. -/
def frobeniusAlong (η : GeometricPoint (space k)) (x : closedPoints (overField k).left)
    (t : fiber k (pointOver k x) ≅ fiber k η) : fundamentalGroup k η :=
  t.conjAut (localFrobenius k x)

theorem frobeniusAlong_app (η : GeometricPoint (space k))
    (x : closedPoints (overField k).left) (t : fiber k (pointOver k x) ≅ fiber k η)
    (V : Cover k) :
    (frobeniusAlong k η x t).hom.app V =
      t.inv.app V ≫ (localFrobenius k x).hom.app V ≫ t.hom.app V := rfl

/-- Canonical label relation over all fiber paths. It selects no unproved witness. -/
def frobeniusClass (η : GeometricPoint (space k)) (x : closedPoints (overField k).left) :
    Set (ConjClasses (fundamentalGroup k η)) :=
  {c | ∃ t : fiber k (pointOver k x) ≅ fiber k η,
    c = ConjClasses.mk (frobeniusAlong k η x t)}

/-- The geometric path theorem and conjugacy show this specified relation has one label. -/
theorem frobeniusClass_unique (η : GeometricPoint (space k))
    (x : closedPoints (overField k).left) : ∃! c, c ∈ frobeniusClass k η x := by
  sorry

/-- The actual degree image is the same inverse residue Frobenius acting on constant fibers. -/
theorem localFrobenius_degree (x : closedPoints (overField k).left) :
    degree k (pointOver k x) (localFrobenius k x) =
      pointAut (constantPoint k (pointOver k x)) (residueSpecIso k x)
        (by change (residueSpecIso k x).hom ≫ ((pointOver k x).hom ≫ structureMap k) = _
            rw [← Category.assoc, residueSpecIso_over]
            rfl) := by
  sorry

end MultiplicativeGroupTame
