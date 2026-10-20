/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Situation_99_16_3_Fiber
public import stacks_project.Chap99.Situation_99_16_3_Category

/-!
# The category of complexes on a proper morphism

Situation 99.16.3 introduces the category of triples `(T, g, E)` consisting of a
scheme over `S`, a morphism `g : T ⟶ B` over `S`, and a complex on the fibre
`X_T` satisfying Lemma 99.16.2 (1)–(2).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes renaming Obj → ComplexesObj

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}



/-- Situation 99.16.3: for a proper, flat, finite-presentation morphism
`f : X ⟶ B` of algebraic spaces over a scheme `S`, `Complexes f` is the category
of triples `(T, g, E)` where `T` is a scheme over `S`, `g : T ⟶ B` is a morphism
over `S`, and setting `X_T = T ×_B X`, the object `E` of `D(𝒪_{X_T})` is
`T`-perfect and has vanishing negative self-Ext groups on field-valued fibres
over `T`. A morphism `(T, g, E) ⟶ (T', g', E')` is a pair `(h, φ)` where
`h : T ⟶ T'` is a morphism of schemes over `B` and
`φ : L(h')^* E' ≅ E` is an isomorphism in `D(𝒪_{X_T})`, where
`h' : X_T ⟶ X_{T'}` is the base change of `h`. -/
@[stacks 0DLE]
abbrev Complexes (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)] [Proper f] [Flat f] [FinitePresentation f] :=
  ComplexesObj f

end AlgebraicGeometry.AlgebraicSpace
