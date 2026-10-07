module

public import ReasLib.Topology.Sheaves.Pullback.IdentityOnOpens
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory.Sheaf

/-- The endomorphism of objectwise sheaf cohomology induced by a self-map that
preserves every open, obtained by transporting `pullbackCohomologyMap` along the
canonical identifications `Opens.map g ≅ 𝟭` and `pullback g ≅ 𝟭`. -/
def cohomologyMapOfPreimageEq {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens X) :
    F.H' p U ⟶ F.H' p U :=
  pullbackCohomologyMap g F p U ≫
    eqToHom
      (congrArg (fun V ↦ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F).H' p V) (hg U)) ≫
    cohomologyMap ((TopCat.Sheaf.pullbackIsoOfPreimageEq g hg).hom.app F) p U

/-- The cohomology endomorphism induced by a self-map preserving every open factors as
pullback on cohomology, transport of the open, and transport of the coefficients. -/
theorem cohomologyMapOfPreimageEq_def {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens X) :
    cohomologyMapOfPreimageEq g hg F p U =
      pullbackCohomologyMap g F p U ≫
        eqToHom
          (congrArg (fun V ↦ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F).H' p V)
            (hg U)) ≫
        cohomologyMap ((TopCat.Sheaf.pullbackIsoOfPreimageEq g hg).hom.app F) p U := sorry

/-- Objectwise, a self-map that preserves every open induces the identity on
`F.H' p U`. -/
theorem cohomologyMapOfPreimageEq_obj_eq_id {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens X) :
    cohomologyMapOfPreimageEq g hg F p U = 𝟙 _ := sorry

/-- A continuous self-map whose inverse image fixes every open induces the identity on
global sheaf cohomology with arbitrary abelian-sheaf coefficients. -/
@[stacks 03SO]
theorem cohomologyMapOfPreimageEq_eq_id {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    cohomologyMapOfPreimageEq g hg F p (⊤ : Opens X) = 𝟙 _ := sorry

end CategoryTheory.Sheaf
