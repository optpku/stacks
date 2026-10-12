/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.FieldValuedPoint

/-!
# Fibre-degree bounds for étale morphisms

This file characterizes uniform fibre-degree bounds for étale morphisms using
the cardinalities of field-valued pullbacks and separably closed fibres.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- For an étale morphism, a uniform bound on fibre degrees is equivalent both to the
corresponding cardinality bound on every field-valued pullback and to that bound after
extension of every residue field to any separable closure. -/
theorem degreesOfFibresBoundedBy_tfae_card_le_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (n : ℕ) :
    List.TFAE
      [ degreesOfFibresBoundedBy f n
      , ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
          Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n
      , ∀ y : Y, ∀ (K : Type u) [Field K] [Algebra (Y.residueField y) K]
          [IsSepClosure (Y.residueField y) K],
          let g : Spec (CommRingCat.of K) ⟶ Y :=
            Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
              Y.fromSpecResidueField y
          Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n
      ] := sorry

/-- For an étale morphism, a natural number bounds all fibre degrees if and only if it
bounds the number of points in every field-valued pullback. -/
theorem degreesOfFibresBoundedBy.iff_fieldValuedPoint_natCard_le_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
        Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n :=
  (degreesOfFibresBoundedBy_tfae_card_le_of_etale f n).out 0 1

/-- For an étale morphism, a natural number bounds all fibre degrees if and only if it
bounds the number of geometric points after every extension of a residue field to a
separable closure. -/
theorem degreesOfFibresBoundedBy.iff_separableClosure_natCard_le_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ y : Y, ∀ (K : Type u) [Field K] [Algebra (Y.residueField y) K]
        [IsSepClosure (Y.residueField y) K],
        let g : Spec (CommRingCat.of K) ⟶ Y :=
          Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
            Y.fromSpecResidueField y
        Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n :=
  (degreesOfFibresBoundedBy_tfae_card_le_of_etale f n).out 0 2

end Scheme.Hom
end AlgebraicGeometry
