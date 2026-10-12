/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction

/-!
# Ringed sites for the small standard topologies

This module equips the selected small Zariski or small étale site with its
canonical structure sheaf and constructs its functorial ringed-site morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology

/-- The selected small Zariski or small étale site, equipped with its canonical
structure sheaf. -/
noncomputable abbrev ringedSite (σ : SmallStandardTopology) (S : Scheme.{u}) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (σ.topology S) <| match σ with
    | .zariski => Scheme.Zariski.Small.structureSheaf S
    | .etale => Scheme.Etale.Small.structureSheaf S

/-- The selected ringed site is the canonical small Zariski or small étale
ringed site in the corresponding branch. -/
theorem ringedSite_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    ringedSite σ S = match σ with
      | .zariski => Scheme.Zariski.Small.ringedSite S
      | .etale => Scheme.Etale.Small.ringedSite S := sorry

/-- The ringed-site morphism induced by a scheme morphism on the selected
small Zariski or small étale site. -/
noncomputable def ringedHom (σ : SmallStandardTopology)
    {S T : Scheme.{u}} (g : T ⟶ S) :
    RingedSite.Hom (ringedSite σ T) (ringedSite σ S) :=
  match σ with
  | .zariski => Scheme.Zariski.Small.ringedHom g
  | .etale => Scheme.Etale.Small.ringedHom g

/-- On the Zariski branch, `ringedHom` is the canonical small-Zariski
ringed-site morphism. -/
theorem ringedHom_zariski {S T : Scheme.{u}} (g : T ⟶ S) :
    ringedHom .zariski g = Scheme.Zariski.Small.ringedHom g := sorry

/-- On the étale branch, `ringedHom` is the canonical small-étale
ringed-site morphism. -/
theorem ringedHom_etale {S T : Scheme.{u}} (g : T ⟶ S) :
    ringedHom .etale g = Scheme.Etale.Small.ringedHom g := sorry

/-- The module direct image along a selected small-site morphism has its
canonical inverse-image left adjoint. -/
theorem ringedHom_modulePushforward_isRightAdjoint
    (σ : SmallStandardTopology) {S T : Scheme.{u}} (g : T ⟶ S) :
    ((ringedHom σ g).modulePushforward.{u}).IsRightAdjoint := sorry

end AlgebraicGeometry.SmallStandardTopology
