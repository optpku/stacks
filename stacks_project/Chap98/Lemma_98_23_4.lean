/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_23_3
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 98.23.4

On a locally Noetherian base, versality of an object of a CFG satisfying
(RS*) at a closed point of a finite-type affine spreads to every finite type
point of some open neighbourhood, given a naive obstruction morphism with
finite homology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open Algebra
open DerivedCategory
open scoped NaiveCotangent
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
variable {ξ : ObjectOverAffineOpen X} [LocallyOfFiniteType ξ.toS]
variable {E : Minus (ModuleCat.{u} ξ.carrier)}
variable (obstructionMap :
    Minus.ι.obj E ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)
variable (u0 : Spec (CommRingCat.of ξ.carrier))
variable [IsFiniteTypePoint u0]

/-- Lemma 98.23.4. Let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf` satisfying (RS*). Let
`U = Spec(A)` be an affine scheme of finite type over `S` which maps into an
affine open `Spec(Λ)`. Let `x` be an object of `X` over `U`. Let
`ξ : E ⟶ NL{A⁄Λ}` be a morphism of `D⁻(A)`. Assume (i) for every deformation
situation `(x, A' → A)`, `x` lifts to `Spec(A')` if and only if
`E ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` is zero, (ii) there is an isomorphism of
functors `T_x(-) ⟶ Ext^0_A(E, -)` such that
`E ⟶ NL{A⁄Λ} ⟶ Ω[A⁄Λ]` corresponds to the canonical element, and (iii)
the cohomology groups of `E` are finite `A`-modules. If `x` is versal at a
closed point `u0 ∈ U`, then there exists an open neighbourhood
`u0 ∈ U' ⊂ U` such that `x` is versal at every finite type point of `U'`. -/
@[stacks 07YN]
theorem exists_isVersalAt_nhd_of_closed
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    (h_finite :
      ∀ i : ℤ,
        Module.Finite ξ.carrier
          ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj (Minus.ι.obj E)))
    [IsVersalAt ξ.toS ξ.obj ξ.over_obj u0]
    (h_closed : IsClosed {u0}) :
    ∃ U' : Opens (Spec (CommRingCat.of ξ.carrier)),
      u0 ∈ U' ∧
        ∀ u, u ∈ U' → IsFiniteTypePoint u →
          IsVersalAt ξ.toS ξ.obj ξ.over_obj u :=
  sorry

/-- Versality at a closed point spreads to every finite type point of some
principal open `D(f)` of `Spec(A)`. -/
theorem exists_basicOpen_isVersalAt_of_closed
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    (h_finite :
      ∀ i : ℤ,
        Module.Finite ξ.carrier
          ((homologyFunctor (ModuleCat.{u} ξ.carrier) i).obj (Minus.ι.obj E)))
    [IsVersalAt ξ.toS ξ.obj ξ.over_obj u0]
    (h_closed : IsClosed {u0}) :
    ∃ f : ξ.carrier,
      u0 ∈ (Spec (CommRingCat.of ξ.carrier)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of ξ.carrier)).inv f) ∧
        ∀ u,
          u ∈ (Spec (CommRingCat.of ξ.carrier)).basicOpen
              ((Scheme.ΓSpecIso (CommRingCat.of ξ.carrier)).inv f) →
            IsFiniteTypePoint u →
              IsVersalAt ξ.toS ξ.obj ξ.over_obj u :=
  sorry

end AlgebraicGeometry.GroupoidsOver
