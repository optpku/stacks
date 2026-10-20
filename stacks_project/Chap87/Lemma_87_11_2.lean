/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Diagonal
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

/- Lemma 87.11.2. The diagonal of a formal algebraic space is representable,
a monomorphism, locally quasi-finite, locally of finite type, and separated. -/
@[stacks 0AIP] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.diagonal_properties :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X],
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
          (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) ∧
      (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) ∧
      (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) ∧
      (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X))
