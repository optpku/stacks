/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.FibreProduct.TorIndependent
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 92.28.1 (1): For Tor-independent algebraic spaces over `B`, the
canonical fibre-product cotangent cone `E` is zero. -/
@[stacks 09DL] #check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.cone_isZero_of_torIndependent :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B),
      TorIndependentOver (Over.mk f) (Over.mk g) → IsZero (cone f g))

/- Lemma 92.28.1 (2): The canonical sum map identifies the cotangent complex
of a Tor-independent fibre product with the sum of the pulled-back complexes. -/
@[stacks 09DL] #check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.sumMap_isIso_of_torIndependent :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B),
      TorIndependentOver (Over.mk f) (Over.mk g) → IsIso (sumMap f g))

#check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.isIsomorphic_cotangent_sumMapSource_of_torIndependent :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B),
      TorIndependentOver (Over.mk f) (Over.mk g) →
        IsIsomorphic (cotangent (toBase f g))
          (DerivedCategory.Q.obj
            (pullbackCotangentCochain (pullback.fst f g) f ⊞
              pullbackCotangentCochain (pullback.snd f g) g)))
