/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernInvertibleSequence

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
open AlgebraicGeometry.AlgebraicSpace.OperationalChow

universe u

open scoped BigOperators

/- Lemma 82.30.2: Total Chern classes multiply in a short exact sequence with invertible submodule. -/
@[stacks 0ES8] #check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.total_eq_mul_of_invertible_shortExact :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (L E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
      [isInvertibleObject L]
      [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
      (ι : L ⟶ E) (q : E ⟶ F)
      (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact),
      (∑ i : Fin (r + 1), homogeneous δ f i.val (chernClass δ f E i.val)) =
      (∑ i : Fin 2, homogeneous δ f i.val (chernClass δ f L i.val)) *
        (∑ i : Fin ((r - 1) + 1), homogeneous δ f i.val (chernClass δ f F i.val)))

#check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.component_eq_add_of_invertible_shortExact :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (L E F : X.Modules) (r : ℕ) (hr : 1 ≤ r)
      [isInvertibleObject L]
      [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F]
      (ι : L ⟶ E) (q : E ⟶ F)
      (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)
      (i : ℕ) (hi : i ≤ r),
      homogeneous δ f i (chernClass δ f E i) =
      homogeneous δ f i (chernClass δ f F i) +
        (if h : 0 < i then
          ringClass f δ L * homogeneous δ f (i - 1 : ℕ) (chernClass δ f F (i - 1))
        else 0))
