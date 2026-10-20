/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.GenericFiberExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Lemma 58.31.8: on an integral normal Noetherian scheme `S`, a smooth morphism
`f : X ⟶ S` with geometrically connected fibres and a section `σ` extends a finite étale
Galois cover of the generic fibre `X_η` with group `G` of order invertible on `S`, given a
`κ(η)`-point over `σ(η)`, to a finite étale Galois cover of `X` with the same group. -/
@[stacks 0EYJ] #check (AlgebraicGeometry.Scheme.FiniteEtale.exists_finiteEtaleGalois_of_genericFiber :
  ∀ {S X : Scheme.{u}} [IsIntegral S] [IsNoetherian S] (hS : S.isNormal)
    {f : X ⟶ S} [Smooth f] [GeometricallyConnected f] (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {G : Type u} [Group G] [Finite G]
    (Z : Scheme.FiniteEtale (f.fiber (genericPoint S)))
    [GaloisCategory (Scheme.FiniteEtale (f.fiber (genericPoint S)))] [IsGalois Z]
    (eG : Aut Z ≃* G) (hinv : IsUnit (Nat.card G : Γ(S, ⊤)))
    (p : Spec (S.residueField (genericPoint S)) ⟶ Z.left)
    (hp : p ≫ Z.hom ≫ f.fiberι (genericPoint S) =
      S.fromSpecResidueField (genericPoint S) ≫ σ),
    ∃ (Y : Scheme.FiniteEtale X) (_ : GaloisCategory (Scheme.FiniteEtale X))
      (_ : IsGalois Y) (_ : Aut Y ≃* G),
      Nonempty ((finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y ≅ Z))

end AlgebraicGeometry.Scheme.FiniteEtale
