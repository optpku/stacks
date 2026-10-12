/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Finite affine families over a scheme

This module owns explicit finite families of affine schemes over a common
target, together with their refinements and componentwise base-change data.
It is independent of a choice of Grothendieck topology or cover condition.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

/-- A finite family of affine schemes mapping to a common base scheme. -/
structure AffineFamilyOver (T : Scheme.{u}) where
  /-- The number of charts. -/
  n : ℕ
  /-- The source schemes of the charts. -/
  U : Fin n → Scheme.{u}
  /-- The chart morphisms to the common target. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each chart source is affine. -/
  isAffine : ∀ j, IsAffine (U j)

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- Construct a finite affine family over a scheme from its chart sources,
maps to the target, and affineness proofs. -/
def of (n : ℕ) (U : Fin n → Scheme.{u}) (map : (j : Fin n) → U j ⟶ T)
    (isAffine : ∀ j, IsAffine (U j)) : AffineFamilyOver T where
  n := n
  U := U
  map := map
  isAffine := isAffine

/-- A refinement of finite affine families over a common target. -/
structure Refinement (refining refined : AffineFamilyOver T) where
  /-- The refined chart through which each refining chart factors. -/
  toIndex : Fin refining.n → Fin refined.n
  /-- The factorization morphisms. -/
  lift : (k : Fin refining.n) → refining.U k ⟶ refined.U (toIndex k)
  /-- Compatibility with the chart maps to the common target. -/
  fac : ∀ k, lift k ≫ refined.map (toIndex k) = refining.map k

/-- Construct a refinement from an index map, component maps, and their
factorization equations. -/
def Refinement.ofMaps {refining refined : AffineFamilyOver T}
    (toIndex : Fin refining.n → Fin refined.n)
    (lift : (k : Fin refining.n) → refining.U k ⟶ refined.U (toIndex k))
    (fac : ∀ k, lift k ≫ refined.map (toIndex k) = refining.map k) :
    Refinement refining refined where
  toIndex := toIndex
  lift := lift
  fac := fac

/-- The factorization equation of a refinement. -/
theorem Refinement.map_eq {refining refined : AffineFamilyOver T}
    (refinement : Refinement refining refined) (k : Fin refining.n) :
    refinement.lift k ≫ refined.map (refinement.toIndex k) = refining.map k := sorry

/-- A componentwise identification of a finite affine family with the base
change of another finite affine family. -/
structure IsBaseChangeOf {S T : Scheme.{u}} (p : T ⟶ S)
    (familyS : AffineFamilyOver S) (familyT : AffineFamilyOver T) where
  /-- The correspondence between chart index sets. -/
  indexEquiv : Fin familyS.n ≃ Fin familyT.n
  /-- The componentwise pullback comparison isomorphisms. -/
  componentIso : ∀ j : Fin familyS.n,
    pullback p (familyS.map j) ≅ familyT.U (indexEquiv j)
  /-- Compatibility of each comparison with the chart map to the new target. -/
  map_eq : ∀ j : Fin familyS.n,
    (componentIso j).hom ≫ familyT.map (indexEquiv j) = pullback.fst p (familyS.map j)

/-- Construct a componentwise base-change identification from an equivalence
of indices, component isomorphisms, and their compatibility with the maps to
the new target. -/
def IsBaseChangeOf.ofComponents {S T : Scheme.{u}} {p : T ⟶ S}
    {familyS : AffineFamilyOver S} {familyT : AffineFamilyOver T}
    (indexEquiv : Fin familyS.n ≃ Fin familyT.n)
    (componentIso : ∀ j : Fin familyS.n,
      pullback p (familyS.map j) ≅ familyT.U (indexEquiv j))
    (map_eq : ∀ j : Fin familyS.n,
      (componentIso j).hom ≫ familyT.map (indexEquiv j) = pullback.fst p (familyS.map j)) :
    IsBaseChangeOf p familyS familyT where
  indexEquiv := indexEquiv
  componentIso := componentIso
  map_eq := map_eq

end AffineFamilyOver

end

end AlgebraicGeometry
