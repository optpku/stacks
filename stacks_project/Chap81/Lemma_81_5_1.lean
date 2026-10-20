/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Etale.Proper

/-!
# Lemma 81.5.1

A proper surjective morphism of algebraic spaces effectively descends étale
morphisms: an étale descent datum relative to such a morphism is isomorphic
to the canonical descent datum of an étale morphism of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData

/- Lemma 81.5.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper surjective
morphism of algebraic spaces over `S`. Any descent datum `(U / X, φ)` relative
to `f` with `U` étale over `X` is effective. More precisely, there exists an
étale morphism `V ⟶ Y` of algebraic spaces whose corresponding canonical
descent datum is isomorphic to `(U / X, φ)`. -/
@[stacks 0GG0] #check (AlgebraicGeometry.AlgebraicSpace.DescentData.existsEtale_of_proper_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [Proper f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [Etale (D.obj ⟨⟩).hom],
    ∃ (V : Over Y) (_ : Etale V.hom),
      Nonempty (ofObj (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) V ≅ D))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.isEffective_of_etale_of_proper_surjective :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [Proper f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [Etale (D.obj ⟨⟩).hom], D.IsEffective)

end AlgebraicGeometry.AlgebraicSpace.DescentData
