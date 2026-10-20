/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Effectivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Étale descent along proper surjective morphisms of algebraic spaces

Étale descent data along a proper surjective morphism are realized by étale
algebraic spaces over the base and are therefore effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData

/-- An étale descent datum relative to a proper surjective morphism of algebraic
spaces over a scheme is isomorphic to the canonical descent datum of an étale
algebraic space over the target. -/
theorem existsEtale_of_proper_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [Proper f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [Etale (D.obj ⟨⟩).hom] :
    ∃ (V : Over Y) (_ : Etale V.hom),
      Nonempty (ofObj (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) V ≅ D) :=
  sorry

/-- A descent datum relative to a proper surjective morphism of algebraic spaces
is effective as soon as its unique component is étale. -/
theorem isEffective_of_etale_of_proper_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [Proper f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [Etale (D.obj ⟨⟩).hom] : D.IsEffective :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DescentData
