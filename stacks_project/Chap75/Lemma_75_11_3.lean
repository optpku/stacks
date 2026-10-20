/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Affine

/-! # Affine identification of the coherator on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 75.11.3 (1). Let `S` be a scheme. Let `X` be an affine algebraic space over `S`.
Set `A = Γ(X, 𝒪_X)`. Then `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` is the functor which sends `F`
to the quasi-coherent `𝒪_X`-module associated to the `A`-module `Γ(X, F)`. -/
@[stacks 08H0] #check (AlgebraicGeometry.AlgebraicSpace.QCoh.affineCoherator_isomorphic :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAffine X],
    IsIsomorphic (QCoh.coherator X) (moduleGlobalSectionsFunctor X ⋙ QCoh.tensorOX X))

/- Lemma 75.11.3 (2). Let `S` be a scheme. Let `X` be an affine algebraic space over `S`.
Set `A = Γ(X, 𝒪_X)`. Then `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` is the functor which sends `E`
to the complex of quasi-coherent `𝒪_X`-modules associated to the object `RΓ(X, E)` of
`D(A)`. -/
@[stacks 08H0] #check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.affineDerivedCoherator_isomorphic :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X],
    IsIsomorphic (QCoh.Derived.coherator X)
      (Modules.moduleDerivedGlobalSections X ⋙ (QCoh.tensorOX X).mapDerivedCategory))

/- Lemma 75.11.3 (3). Let `S` be a scheme. Let `X` be an affine algebraic space over `S`.
Restricted to `D_QCoh(𝒪_X)`, the functor `RQ_X` is a quasi-inverse to the comparison
`D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 08H0] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affineCoherator_isQuasiInverse :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X],
    (DerivedQCoh.comparison X).IsQuasiInverse
      (DerivedQCoh.inclusion X ⋙ QCoh.Derived.coherator X))

end AlgebraicGeometry.AlgebraicSpace
