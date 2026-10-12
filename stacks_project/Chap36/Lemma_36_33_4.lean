/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FlatPullbackSections

open RingedSpace.ModuleDerived CategoryTheory.HomotopyColimit

/- Lemma 36.33.4 (1): for a flat finitely presented map `f : U ⟶ X`, with `X`
finitely presented over `A`, there is an inverse system `L : ℕᵒᵖ ⥤ D(𝒪_X)` of perfect
objects such that `K ↦ RΓ(U, Lf^*K)` is functorially its sequential `RHom` homotopy-colimit
presentation in `D(A)`. -/
@[stacks 0CRR] #check
  (AlgebraicGeometry.Scheme.FlatPullbackSections.exists_perfect_rHom :
    ∀ {A : Type u} [CommRing A] {X U : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of A)) (f : U ⟶ X)
      [Scheme.Hom.FinitePresentation x] [Flat f] [Scheme.Hom.FinitePresentation f]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)],
      ∃ L : ℕᵒᵖ ⥤ RingedSpace.ModuleDerived X.toRingedSpace,
        (∀ n : ℕ, IsPerfect (L.obj (Opposite.op n))) ∧
          Functorial.IsOf (rHomDiagram x L) (pullbackFunctor x f))

/- Lemma 36.33.4 (2): for a flat finitely presented map `f : U ⟶ X`, with `X`
finitely presented over `A`, there is a direct system `E : ℕ ⥤ D(𝒪_X)` of perfect objects
such that `K ↦ RΓ(U, Lf^*K)` is functorially the sequential homotopy colimit of
`K ↦ RΓ(X, Eₙ ⊗ᴸ K)` in `D(A)`. -/
@[stacks 0CRR] #check
  (AlgebraicGeometry.Scheme.FlatPullbackSections.exists_perfect_tensor :
    ∀ {A : Type u} [CommRing A] {X U : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of A)) (f : U ⟶ X)
      [Scheme.Hom.FinitePresentation x] [Flat f] [Scheme.Hom.FinitePresentation f]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [Tensor.Has X.toRingedSpace],
      ∃ E : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace,
        (∀ n : ℕ, IsPerfect (E.obj n)) ∧
          Functorial.IsOf (tensorDiagram x E) (pullbackFunctor x f))

end AlgebraicGeometry.Scheme.FlatPullbackSections
