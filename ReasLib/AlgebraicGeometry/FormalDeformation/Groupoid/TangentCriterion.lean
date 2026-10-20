/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Minimality
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section

/-!
# Tangent criteria for normalized and minimal groupoids

The quotient tangent comparison sends a dual-number point to the isomorphism class
of its quotient fibre object. For smooth prorepresentable groupoids, this map
characterizes normalization and minimality.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- The quotient tangent space is the type of isomorphism classes of objects in
the dual-number fibre of the quotient projection. -/
abbrev quotientTangentSpace
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :=
  isomorphismClasses.obj (Cat.of (G.forget.Fiber (dualNumber Λ k)))

/-- The quotient tangent comparison sends a dual-number point to the isomorphism
class of its actual quotient object in the dual-number fibre. -/
def quotientTangentSpaceMap
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    (x : G.U.obj (dualNumber Λ k)) : quotientTangentSpace G :=
  Quotient.mk'' (Functor.Fiber.mk (p := G.forget)
    (a := G.quotientObj (dualNumber Λ k) x) (G.forget_obj (dualNumber Λ k) x))

/-- The quotient tangent comparison is represented by the quotient object of its
dual-number input, equipped with its canonical base equality. -/
theorem quotientTangentSpaceMap_apply
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    (x : G.U.obj (dualNumber Λ k)) :
    quotientTangentSpaceMap G x =
      Quotient.mk'' (Functor.Fiber.mk (p := G.forget)
        (a := G.quotientObj (dualNumber Λ k) x) (G.forget_obj (dualNumber Λ k) x)) := rfl

/-- A smooth prorepresentable groupoid is normalized exactly when its quotient
tangent comparison is bijective. -/
theorem isNormalized_iff_bijective_quotientTangentSpaceMap
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    IsNormalized G ↔ Function.Bijective (quotientTangentSpaceMap G) := sorry

/-- A smooth prorepresentable groupoid is minimal exactly when every tangent
point mapping to the quotient origin is induced by a residue-field derivation.
The origin and derivation image are computed from any residue-field value. -/
theorem isMinimal_iff_ker_quotientTangentSpaceMap_le_range_ofDerivation
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    IsMinimal G ↔
      ∀ (x0 : G.U.obj (residue Λ k)) (x : G.U.obj (dualNumber Λ k)),
        quotientTangentSpaceMap G x =
          quotientTangentSpaceMap G (G.U.map (residueToDualNumber Λ k) x0) →
        x ∈ Set.range (fun D : Derivation Λ k k ↦
          G.U.map (derivationToDualNumber D) x0) := sorry

end CategoryTheory.GroupoidInFunctors
