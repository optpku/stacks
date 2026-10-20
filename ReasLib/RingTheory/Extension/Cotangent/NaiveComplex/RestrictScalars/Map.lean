/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Target-changing maps of naive cotangent complexes

This leaf extends presentation-level functoriality to a morphism whose target
algebra changes.  The target naive complex is viewed over the old target ring
by restriction of scalars, so the construction is usable for arbitrary
commutative squares of algebra presentations.
-/

@[expose] public section

open CategoryTheory

universe u v w x

noncomputable section

namespace Algebra.Extension.NaiveCotangent.RestrictScalars

variable {R : Type u} {R' : Type v} {S S' : Type w}
variable [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

namespace Map

/-- The degree-zero component of the target-changing map of naive cotangent
complexes induced by a morphism of presentations. -/
noncomputable def zero
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    (complex P).X 0 ⟶ (restrictScalars Q S).X 0 :=
  ModuleCat.ofHom (CotangentSpace.map f) ≫
    (ModuleCat.RestrictScalars.identityIso (R := S) (S := S') Q.CotangentSpace).inv

/-- The degree-one component of the target-changing map of naive cotangent
complexes induced by a morphism of presentations. -/
noncomputable def one
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    (complex P).X 1 ⟶ (restrictScalars Q S).X 1 :=
  ModuleCat.ofHom
      ((liftEquiv Q).symm.toLinearMap.restrictScalars S ∘ₗ
        Cotangent.map f ∘ₗ (liftEquiv P).toLinearMap) ≫
    (ModuleCat.RestrictScalars.identityIso (R := S) (S := S') (Lift Q)).inv

/-- The degree-one and degree-zero components of the target-changing map
commute with their differentials. -/
theorem oneZeroComm
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    one f ≫ (restrictScalars Q S).d 1 0 =
      (complex P).d 1 0 ≫ zero f := sorry

/-- The zero higher component satisfies the inductive chain-map compatibility
condition for a target-changing map. -/
theorem succComm
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) (n : ℕ)
    (p :
      Σ' (zero : (complex P).X n ⟶ (restrictScalars Q S).X n)
          (one : (complex P).X (n + 1) ⟶ (restrictScalars Q S).X (n + 1)),
        one ≫ (restrictScalars Q S).d (n + 1) n =
          (complex P).d (n + 1) n ≫ zero) :
    (0 : (complex P).X (n + 2) ⟶ (restrictScalars Q S).X (n + 2)) ≫
        (restrictScalars Q S).d (n + 2) (n + 1) =
      (complex P).d (n + 2) (n + 1) ≫ p.2.1 := sorry

/-- The higher components of a target-changing map of naive cotangent
complexes are canonically zero. -/
noncomputable def succ
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) (n : ℕ)
    (p :
      Σ' (zero : (complex P).X n ⟶ (restrictScalars Q S).X n)
          (one : (complex P).X (n + 1) ⟶ (restrictScalars Q S).X (n + 1)),
        one ≫ (restrictScalars Q S).d (n + 1) n =
          (complex P).d (n + 1) n ≫ zero) :
    Σ' two : (complex P).X (n + 2) ⟶ (restrictScalars Q S).X (n + 2),
      two ≫ (restrictScalars Q S).d (n + 2) (n + 1) =
        (complex P).d (n + 2) (n + 1) ≫ p.2.1 :=
  ⟨0, succComm f n p⟩

end Map

/-- The map of naive cotangent complexes induced by a morphism of
presentations with a changing target algebra. -/
@[stacks 07VC "target-changing naive cotangent map"]
noncomputable def map
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    complex P ⟶ restrictScalars Q S :=
  ChainComplex.mkHom _ _
    (Map.zero f)
    (Map.one f)
    (Map.oneZeroComm f)
    (Map.succ f)

/-- The degree-lowering data that compares target-changing maps induced by
two parallel morphisms of presentations. -/
@[stacks 07VC "target-changing naive cotangent homotopy"]
noncomputable def homotopyMap
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    (complex P).X i ⟶ (restrictScalars Q S).X j :=
  match i, j with
  | 0, 1 =>
      ModuleCat.ofHom ((liftEquiv Q).symm.toLinearMap.restrictScalars S ∘ₗ f.sub g) ≫
        (ModuleCat.RestrictScalars.identityIso (R := S) (S := S') (Lift Q)).inv
  | _, _ => 0

/-- The difference of target-changing maps associated to two parallel
presentation morphisms is null-homotopic. -/
@[stacks 07VC "target-changing naive cotangent homotopy"]
theorem map_sub_eq_nullHomotopicMap
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f g : P.Hom Q) :
    map f - map g = Homotopy.nullHomotopicMap' (homotopyMap f g) := sorry

/-- Parallel target-changing maps of naive cotangent complexes are
canonically chain-homotopic. -/
@[stacks 07VC "target-changing naive cotangent homotopy"]
noncomputable def mapHomotopy
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f g : P.Hom Q) :
    Homotopy (map f) (map g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (map_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (homotopyMap f g)))

end Algebra.Extension.NaiveCotangent.RestrictScalars
