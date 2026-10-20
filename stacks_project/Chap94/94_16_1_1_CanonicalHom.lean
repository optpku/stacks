/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalHom
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Canonical fibre morphisms of a self 2-fibre product

A morphism `φ : a ⟶ b` in `[U/R]` over `T` is represented by a switched object
`(b, a, α)` of the fibrewise categorical pullback of `fiberFunctor f T` with
itself. The associated fibre morphism is `α.inv : f(a) ⟶ f(b)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.ofSwitchedComparison :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}
    (a b : U.p.Fiber T),
    ((fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) →
      (fiberFunctor f T) ⊡ (fiberFunctor f T))

#check (AlgebraicGeometry.ofSwitchedComparison_fst :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}
    (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a),
    (AlgebraicGeometry.ofSwitchedComparison f a b α).fst = b)

#check (AlgebraicGeometry.ofSwitchedComparison_snd :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}
    (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a),
    (AlgebraicGeometry.ofSwitchedComparison f a b α).snd = a)

#check (AlgebraicGeometry.ofSwitchedComparison_iso :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}
    (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a),
    (AlgebraicGeometry.ofSwitchedComparison f a b α).iso = α)

#check (AlgebraicGeometry.canonicalHom :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}
    (φ : (fiberFunctor f T) ⊡ (fiberFunctor f T)),
    (fiberFunctor f T).obj φ.snd ⟶ (fiberFunctor f T).obj φ.fst)

#check (AlgebraicGeometry.canonicalHom_apply :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}
    (φ : (fiberFunctor f T) ⊡ (fiberFunctor f T)),
    AlgebraicGeometry.canonicalHom f φ = φ.iso.inv)

end AlgebraicGeometry
