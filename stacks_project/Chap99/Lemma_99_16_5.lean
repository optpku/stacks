/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Lemma_99_16_5_Isom

/-!
# Lemma 99.16.5

In Situation 99.16.3 the diagonal of the category of complexes is representable
by algebraic spaces, in the sense of Algebraic Stacks, Lemma 94.10.11 (1):
fibrewise Isom presheaves are algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.16.5: in Situation 99.16.3, with `𝒳 = Complexes f`, the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. At Hom-universe `u + 1`
this is the 94.10.11(1) condition that for every scheme `T` over `S` and
objects `x, y` of the fibre `𝒳_T`, the presheaf `Isom_𝒳(x, y)` is an algebraic
space over `T`. -/
@[stacks 0DLG]
theorem isom_isAlgebraicSpace (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    [Functor.IsFibered (p f)] : isAlgebraicSpace f := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
