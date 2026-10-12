/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Situation_99_14_1_Category

/-!
# The stack of polarized proper schemes

Situation 99.14.1 introduces the category of pairs consisting of a proper flat
finite-presentation morphism of schemes and a relatively ample invertible
module on the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Polarized (Obj p)

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Situation 99.14.1: the category Polarized of pairs `(X ⟶ S, L)` where
`X ⟶ S` is a proper, flat, finite-presentation morphism of schemes and `L` is
an invertible `O_X`-module which is relatively ample on `X / S`. A morphism
`(X' ⟶ S', L') ⟶ (X ⟶ S, L)` is a triple `(f, g, φ)` with `f : X' ⟶ X` and
`g : S' ⟶ S` forming a cartesian square and `φ : f^* L ≅ L'` an isomorphism.
The forgetful functor `p : Polarized ⥤ Scheme`, `(X ⟶ S, L) ↦ S`, presents
Polarized as a category over `Sch_fppf`. -/
@[stacks 0D1M]
abbrev Polarized := Obj

/-- The forgetful functor of Polarized sends each polarized pair to its base
scheme. -/
theorem Polarized.forget_obj (x : Polarized) : p.obj x = x.S :=
  sorry

end AlgebraicGeometry
