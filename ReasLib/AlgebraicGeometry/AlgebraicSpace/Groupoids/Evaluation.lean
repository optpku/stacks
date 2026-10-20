/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom

/-! # Evaluation of morphisms between represented groupoid fibrations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory

noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.toGroupoids
variable {S : Scheme.{u}}

/-- On objects, a presented `1`-morphism agrees with the canonical `1`-morphism associated to
its recovered algebraic-space map. -/
theorem evalMap_obj_eq {F G : AlgebraicSpace S}
    (ψ : F.toGroupoids ⟶ G.toGroupoids) :
    ∀ x, ψ.hom.obj x = (map (eval ψ)).hom.obj x :=
  sorry

/-- The morphism of presented groupoid fibrations associated to `ψ` is 2-isomorphic to
`map (eval ψ)`. -/
def evalMapIso {F G : AlgebraicSpace S} (ψ : F.toGroupoids ⟶ G.toGroupoids) :
    ψ ≅ map (eval ψ) :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (fun x => eqToIso (evalMap_obj_eq ψ x))
      (fun {_ _} _ => sorry) (fun _ => sorry))


end AlgebraicGeometry.AlgebraicSpace.toGroupoids
