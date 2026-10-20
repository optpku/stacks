/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Map
public import ReasLib.AlgebraicGeometry.ChowGroup.VectorBundle.ShortExact

/-!
# Associated vector-bundle maps
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.AssociatedVectorBundle
open ChowGroup.AssociatedVectorBundle

#check (Scheme.AssociatedVectorBundle.ShortExact.embedding :
  ∀ {S : Scheme.{u}} (X : Over S) (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₂)))
    [Scheme.IsRelativeSpectrumOver P₂],
    Scheme.associatedVectorBundle (Scheme.Modules.dual C.X₁) P₁ ⟶
      Scheme.associatedVectorBundle (Scheme.Modules.dual C.X₂) P₂)

#check (ChowGroup.AssociatedVectorBundle.ShortExact.pushforward :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) (r₁ r₃ : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₁ C.X₁]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (r₁ + r₃) C.X₂]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₃ C.X₃]
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₂)))
    [Scheme.IsRelativeSpectrumOver P₂] (n : ℤ),
    relativeChow delta X (Scheme.Modules.dual C.X₁) P₁ n →+
      relativeChow delta X (Scheme.Modules.dual C.X₂) P₂ n)

end AlgebraicGeometry
