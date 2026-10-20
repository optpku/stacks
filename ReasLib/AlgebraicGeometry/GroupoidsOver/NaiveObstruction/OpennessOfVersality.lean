module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstruction.VersalAt

/-! # Openness of versality from a naive obstruction morphism -/

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

/-- For an affine finite-type object over a locally Noetherian base satisfying
(RS*), a bounded-above obstruction morphism detecting lifts, matching the canonical
tangent element, and having finite cohomology makes versality at a closed point
spread to every finite type point of some principal open neighbourhood. -/
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

/-- For an affine finite-type object over a locally Noetherian base satisfying
(RS*), a bounded-above obstruction morphism detecting lifts, matching the canonical
tangent element, and having finite cohomology makes versality at a closed point
spread to every finite type point of some open neighbourhood. -/
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

end AlgebraicGeometry.GroupoidsOver
