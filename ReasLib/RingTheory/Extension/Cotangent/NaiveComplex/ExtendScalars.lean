/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension-of-scalars maps of naive cotangent complexes

@stack 07VC

This leaf is adjoint to the target-changing restriction-of-scalars map.  A
morphism of presentations whose target algebra changes induces a map from the
scalar extension of the source naive cotangent complex to the target naive
cotangent complex.
-/

@[expose] public section

open CategoryTheory

universe u v w x

noncomputable section

namespace Algebra.Extension.NaiveCotangent.ExtendScalars

variable {R : Type u} {R' : Type v} {S S' : Type w}
variable [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable [Algebra R R'] [Algebra S S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

/-- The literal scalar extension of the naive cotangent complex of `P` along
the target map `S → S'`. -/
@[stacks 07VC "target-changing naive cotangent map"]
noncomputable abbrev source
    (P : Extension.{x} R S) : ChainComplex (ModuleCat.{max w x} S') ℕ :=
  ((ModuleCat.extendScalars (algebraMap S S')).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (complex P)

namespace Map

/-- The degree-zero component of the scalar-extended target-changing map. -/
noncomputable def zero
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    (source P).X 0 ⟶ (complex Q).X 0 :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap S S')).homEquiv _ _).symm
    (RestrictScalars.Map.zero f)

/-- The degree-one component of the scalar-extended target-changing map. -/
noncomputable def one
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    (source P).X 1 ⟶ (complex Q).X 1 :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap S S')).homEquiv _ _).symm
    (RestrictScalars.Map.one f)

/-- The degree-one and degree-zero components of the scalar-extended map
commute with their differentials. -/
theorem oneZeroComm
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    one f ≫ (complex Q).d 1 0 = (source P).d 1 0 ≫ zero f := sorry

/-- The zero higher component satisfies the inductive chain-map compatibility
condition for a scalar-extended target-changing map. -/
theorem succComm
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) (n : ℕ)
    (p :
      Σ' (zero : (source P).X n ⟶ (complex Q).X n)
          (one : (source P).X (n + 1) ⟶ (complex Q).X (n + 1)),
        one ≫ (complex Q).d (n + 1) n = (source P).d (n + 1) n ≫ zero) :
    (0 : (source P).X (n + 2) ⟶ (complex Q).X (n + 2)) ≫
        (complex Q).d (n + 2) (n + 1) =
      (source P).d (n + 2) (n + 1) ≫ p.2.1 := sorry

/-- The higher components of a scalar-extended target-changing map are
canonically zero. -/
noncomputable def succ
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) (n : ℕ)
    (p :
      Σ' (zero : (source P).X n ⟶ (complex Q).X n)
          (one : (source P).X (n + 1) ⟶ (complex Q).X (n + 1)),
        one ≫ (complex Q).d (n + 1) n = (source P).d (n + 1) n ≫ zero) :
    Σ' two : (source P).X (n + 2) ⟶ (complex Q).X (n + 2),
      two ≫ (complex Q).d (n + 2) (n + 1) =
        (source P).d (n + 2) (n + 1) ≫ p.2.1 :=
  ⟨0, succComm f n p⟩

end Map

/-- A morphism of presentations with a changing target algebra induces a map
from the scalar extension of the source naive cotangent complex to the target
naive cotangent complex. -/
@[stacks 07VC "target-changing naive cotangent map"]
noncomputable def map
    {P : Extension.{x} R S} {Q : Extension.{x} R' S'} (f : P.Hom Q) :
    source P ⟶ complex Q :=
  ChainComplex.mkHom _ _
    (Map.zero f)
    (Map.one f)
    (Map.oneZeroComm f)
    (Map.succ f)

end Algebra.Extension.NaiveCotangent.ExtendScalars
