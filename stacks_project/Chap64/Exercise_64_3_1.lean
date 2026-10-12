/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.IdentityOnOpens
import StacksCheckRecall

/-!
# Identity-on-opens self-maps act as the identity on sheaf cohomology

If a continuous self-map of a space induces the identity functor on opens, then
pullback of abelian sheaves is canonically the identity functor, and the induced
endomorphism of objectwise sheaf cohomology is the identity.
-/

@[expose] public section

open CategoryTheory TopologicalSpace TopCat

universe u

/- Exercise 64.3.1: if `g : X ⟶ X` is a continuous self-map with
`(Opens.map g).obj U = U` for every open `U` of `X` (equivalently `g ⁻¹' U = U`
as sets; see `Opens.map_obj_eq_iff`), then `g` induces the identity on sheaf
cohomology of `X` for an arbitrary abelian sheaf. -/
@[stacks 03SO] #check (CategoryTheory.Sheaf.cohomologyMapOfPreimageEq_eq_id :
  ∀ {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ),
    CategoryTheory.Sheaf.cohomologyMapOfPreimageEq g hg F p (⊤ : Opens X) = 𝟙 _)
