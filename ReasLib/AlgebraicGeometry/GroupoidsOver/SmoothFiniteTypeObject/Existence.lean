/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FiniteDimensionalPredeformations
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothFiniteTypeObject

/-!
# Existence of smooth finite-type charts

If `S` is locally Noetherian, `X` is a category fibred in groupoids over
`(Sch/S)_fppf` whose diagonal is representable by algebraic spaces, and `X`
is limit preserving, has the Rim–Schlessinger property and finite-dimensional
predeformations, has effective formal objects, and satisfies openness of versality,
then every finite-type residue object over a G-ring stalk is
approximated by a smooth finite-type 2-Yoneda 1-morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Let `S` be a locally Noetherian scheme, let `X` be a category
fibred in groupoids over `(Sch/S)_fppf`, and let `k` be a finite type field over
`S` with an object `x0` of `X` over `Spec(k)` with image `s`. Assume the
diagonal `Δ : X ⟶ X × X` is representable by algebraic spaces, `X` satisfies
limit preservation, the Rim–Schlessinger property, and finite-dimensional
predeformations, every formal object of `X` is effective, openness of
versality holds for `X`, and `𝒪_{S,s}` is a G-ring. Then there exist a finite
type morphism `U ⟶ S` and an object `x` of `X` over `U` such that the 2-Yoneda
1-morphism `(Sch/U)_fppf ⟶ X` is smooth, and a finite type point `u0` of `U`
with residue field `k` such that `x|_{u0} ≅ x0`. -/
theorem nonempty_smoothFiniteTypeObject {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X] [OpennessOfVersality X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObject X, FormalObject.IsEffective ξ)
    {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType kToS] (x0 : X.p.Fiber (Over.mk kToS)) (s : S)
    (hs : kToS (closedPoint k) = s) [IsGRing (S.presheaf.stalk s)] :
    Nonempty (SmoothFiniteTypeObject kToS x0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
