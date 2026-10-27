/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AbsoluteSeparation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u v

/- Definition 87.16.3 (1): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. We say `X` is quasi-separated if the equivalent conditions of
Lemma 87.16.1 are satisfied. -/
@[stacks 0AJ7] #check
  (AlgebraicGeometry.IsFormalAlgebraicSpace.IsQuasiSeparated :
    ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      [AlgebraicGeometry.IsFormalAlgebraicSpace X], Prop)

/- Definition 87.16.3 (2): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. We say `X` is separated if the equivalent conditions of
Lemma 87.16.2 are satisfied. -/
@[stacks 0AJ7] #check
  (AlgebraicGeometry.IsFormalAlgebraicSpace.IsSeparated :
    ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      [AlgebraicGeometry.IsFormalAlgebraicSpace X], Prop)
