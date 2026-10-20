/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.CategoryTheory.Groupoid.Quotient

/-!
# Smoothness of groupoids and their quotient morphisms

A groupoid in functors on `ArtinianLocalAlgCat Λ k` is smooth exactly when
its source map, its target map, or its canonical quotient morphism is smooth.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Smooth groupoids in functors on `ArtinianLocalAlgCat Λ k` need not have
smooth quotients as categories cofibered in groupoids. -/
theorem not_forall_isSmooth_quotient :
    ¬ ∀ (G : GroupoidInFunctors.{u + 1, u, max u v} (ArtinianLocalAlgCat Λ k)),
      IsSmooth G.s G.t → Functor.IsSmooth G.quotient.p :=
  sorry

/-- For a groupoid in functors on `ArtinianLocalAlgCat Λ k`, smoothness of the
groupoid, its source map, its target map, and its canonical quotient morphism
are equivalent. -/
theorem isSmooth_tfae (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    List.TFAE [IsSmooth G.s G.t, NatTrans.IsSmooth G.s, NatTrans.IsSmooth G.t,
      BasedFunctor.IsSmooth (quotientMorphism G)] :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of the source
map. -/
theorem isSmooth_iff_source (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    IsSmooth G.s G.t ↔ NatTrans.IsSmooth G.s :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of the target
map. -/
theorem isSmooth_iff_target (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    IsSmooth G.s G.t ↔ NatTrans.IsSmooth G.t :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of its canonical
quotient morphism. -/
theorem isSmooth_iff_quotientMorphism
    (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    IsSmooth G.s G.t ↔ BasedFunctor.IsSmooth (quotientMorphism G) :=
  sorry

end CategoryTheory.GroupoidInFunctors
