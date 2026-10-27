/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernClass.ProjectiveRelation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open scoped BigOperators

universe u

/- Lemma 82.28.1: For a finite locally free module of any finite rank, the
normalized Chow cap maps satisfying the alternating tautological projective
relation exist uniquely on every good test space. These maps are the cap actions
of the operational Chern classes, as identified by the checks below. -/
@[stacks 0ERY] #check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.existsUnique_projective_caps :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)],
      ∃! c : ∀ i : Fin (r + 1), ∀ k : ℤ,
        Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val),
        (∀ k : ℤ, c 0 k =
          (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom) ∧
        (∀ (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
          ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
            AlgebraicGeometry.AlgebraicSpace.ChernClass.projectiveRelationTerm
              δ f E r g c k i α = 0))

#check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ),
      OperationalChow δ f (i : ℤ))

#check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass_cap_of_constantRank :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (i : ℕ) (k : ℤ),
      (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass δ f E i).cap g k =
        ConstantRankChern.cap (g ≫ f) δ ((Modules.pullback g).obj E) r i k)

#check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass_cap_zero :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass δ f E 0).cap g k =
        (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom)

#check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.projective_relation :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
        AlgebraicGeometry.AlgebraicSpace.ChernClass.projectiveRelationTerm δ f E r g
          (fun i k =>
            (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass δ f E i.val).cap g k)
          k i α = 0)
