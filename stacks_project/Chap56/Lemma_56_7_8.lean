/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import stacks_project.Chap56.Lemma_56_7_5_Functor

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/-- Lemma 56.7.8: if `k` is a field and `X`, `Y` are finite-type schemes over `k`
with `X` separated and `Y` reduced, then every `k`-linear equivalence
`F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace` is given,
up to objectwise isomorphism, by pullback along an isomorphism `f : Y ≅ X` over
`k` (that is, `f.hom ≫ x = y`) followed by tensoring with an invertible `O_Y`-module `L`. Informal
`F(𝓕) = f^* 𝓕 ⊗ L` is this objectwise isomorphism; the proof may recover
`f = pr₁ ∘ s` from Lemma 56.7.6, but that reconstruction is not a second labeled
clause. -/
@[stacks 0FZR]
theorem coherent_equivalence_pullback_tensor_invertible_over_field
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
    [x.FiniteType] [y.FiniteType] [IsSeparated x] [IsReduced Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    [F.IsEquivalence] [LinearOverCoh x y F] :
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Scheme.Modules.Invertible L ∧
        f.hom ≫ x = y ∧
          ∀ 𝓕 : RingedSpace.Coh X.toRingedSpace,
            Nonempty ((F.obj 𝓕).obj ≅
              (CategoryTheory.MonoidalCategory.tensorRight L).obj
                ((Scheme.Modules.pullback f.hom).obj 𝓕.obj)) := sorry
