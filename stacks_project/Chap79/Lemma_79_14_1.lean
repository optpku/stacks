/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.FinitePart
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 79.14.1. A groupoid with separated, locally finite type source and target
has its canonical finite-part groupoid and universal finite family containing the unit. -/
@[stacks 04RU] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.finitePart_spec :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left],
    (finitePartHom G).obj.left =
        FinitePart.withSectionToY G.s.left G.e.left (unit_source_left G) ∧
      (finitePartHom G).arrow.left = univToR G ∧
      AlgebraicSpace.Etale (finitePartHom G).obj.left ∧
      AlgebraicSpace.IsOpenImmersion (univι G) ∧
      AlgebraicSpace.IsClosedImmersion (univι G) ∧
      AlgebraicSpace.IsFinite
        (univι G ≫ pullback.fst (finitePartHom G).obj.left G.s.left) ∧
      unitLeft G ≫ univι G = unitBaseChange G ∧
      ∀ {T : Over S}
        (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
        (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a),
        factorsThroughOpen G p z ↔ factorsThroughUnivι G (univPoint G p z hz))

end AlgebraicGeometry.GroupoidAlgebraicSpace
