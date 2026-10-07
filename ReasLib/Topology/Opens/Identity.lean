module

public import Mathlib.Topology.Category.TopCat.Opens

@[expose] public section

open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u

namespace TopologicalSpace.Opens

/-- The functor `Opens.map g` is canonically isomorphic to the identity on opens whenever
`g` pulls every open set back to itself. -/
def mapIsoIdOfPreimageEq {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U) :
    Opens.map g ≅ 𝟭 (Opens X) :=
  NatIso.ofComponents (fun U ↦ eqToIso (hg U)) (fun {_ _} _ ↦ Subsingleton.elim _ _)

/-- The component of `mapIsoIdOfPreimageEq` at an open is `eqToHom` of the given equality. -/
theorem mapIsoIdOfPreimageEq_hom_app {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U) (U : Opens X) :
    (mapIsoIdOfPreimageEq g hg).hom.app U = eqToHom (hg U) := sorry

/-- Equality of opens after `Opens.map g` is the set-theoretic preimage condition
`g ⁻¹' U = U`. -/
theorem map_obj_eq_iff {X : TopCat.{u}} (g : X ⟶ X) (U : Opens X) :
    (Opens.map g).obj U = U ↔ g ⁻¹' (U : Set X) = (U : Set X) := sorry

end TopologicalSpace.Opens
