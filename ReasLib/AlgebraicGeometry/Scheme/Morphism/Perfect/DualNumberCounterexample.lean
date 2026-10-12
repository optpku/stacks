/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DualNumber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.Perfect.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.DualNumber

/-- Over a field `k`, the point `Spec(k)` is perfect over itself. -/
@[instance]
theorem point_isPerfectOverBase (k : Type u) [Field k] :
    LocallyOfType RingHom.IsPerfectRingMap (𝟙 (Spec (CommRingCat.of k))) := sorry

/-- The dual-number thickening `Spec(DualNumber k)` is perfect over `Spec(k)`. -/
@[instance]
theorem thickening_isPerfectOverBase (k : Type u) [Field k] :
    LocallyOfType RingHom.IsPerfectRingMap
      (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) := sorry

/-- A morphism from `Spec(k)` to the dual-number thickening is over `Spec(k)` exactly when
it is induced by the canonical residue projection `DualNumber k →+* k`. -/
theorem overBase_iff_eq_reduction (k : Type u) [Field k]
    (f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k))) :
    f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) =
        𝟙 (Spec (CommRingCat.of k)) ↔
      f = Spec.map
        (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := sorry

/-- The residue-induced morphism from `Spec(k)` to its dual-number thickening is not
perfect. -/
theorem reduction_not_perfect (k : Type u) [Field k] :
    ¬ LocallyOfType RingHom.IsPerfectRingMap
      (Spec.map
        (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) := sorry

/-- Over any field, the point and its dual-number thickening are perfect over the point,
the residue-induced morphism is the unique morphism over the point, and it is not perfect. -/
theorem perfectOverBase_and_reduction_not_perfect (k : Type u) [Field k] :
    LocallyOfType RingHom.IsPerfectRingMap (𝟙 (Spec (CommRingCat.of k))) ∧
      LocallyOfType RingHom.IsPerfectRingMap
        (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ∧
      (∀ f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)),
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) =
            𝟙 (Spec (CommRingCat.of k)) ↔
          f = Spec.map
            (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ∧
      ¬ LocallyOfType RingHom.IsPerfectRingMap
        (Spec.map
          (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) := sorry

end AlgebraicGeometry.DualNumber
