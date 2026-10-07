module

public import stacks_project.Chap98.«98_13_2_1_Smooth»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equation-smooth 1-morphisms of groupoid fibrations

Stacks tag 07XS: a 1-morphism of categories fibred in groupoids over a locally
Noetherian base satisfies (equation-smooth) when it induces a smooth map of
predeformation categories at every finite-type field-valued point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- 98.13.2.1: for all fields `k` of finite type over `S` and all `x0` in the
fibre of `X` over `Spec(k)`, the map of predeformation categories
`ℱ_{X, k, x0} ⟶ ℱ_{Y, k, f(x0)}` is smooth. -/
@[stacks 07XS]
theorem isSmoothOnPredeformations_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    IsSmoothOnPredeformations f ↔
      ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
        [Module.Finite Λ k]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
        (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
        (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
        (x0 : X.p.Fiber (Over.mk kToS)),
        IsSmoothAt f openImmersion kToS h_factor x0 :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
