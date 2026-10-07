module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.DirectLimit.Descent

/-!
# The descended direct-limit cocone of a refinement-stage diagram

This file exposes the public descended system, its stage inclusions, and the resulting lower
refinement cocone.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedPreorderSystem.StageDiagram

variable {δ : Type d} [Preorder δ] [IsDirectedOrder δ]
variable (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)

/-- The inverse-system diagram descended from the direct-limit index. -/
noncomputable def colimit_system : D.index_preordᵒᵖ ⥤ C :=
  Descent.system D

/-- The canonical isomorphism from a stage diagram to the descended system restricted along its
direct-limit inclusion. -/
noncomputable def colimit_inclusion_iso (a : δ) :
    (D.obj a).diagram ≅
      ((D.index_inclusion a).toOrderHom.toFunctor).op ⋙ D.colimit_system :=
  Descent.iso D a

/-- The bundled pure refinement from one stage into the descended direct-limit system. -/
noncomputable def colimit_inclusion (a : δ) :
    OrderedRefinement (D.obj a).diagram D.colimit_system :=
  OrderedRefinement.ofEmbedding (D.index_inclusion a) D.colimit_system
    (D.colimit_inclusion_iso a)

/-- The bundled colimit inclusion is natural along a diagram transition. -/
theorem colimit_inclusion_natural {a b : δ} (hab : a ≤ b) (i : (D.obj a).index) :
    (D.colimit_inclusion a).embedding i =
      (D.colimit_inclusion b).embedding (D.index_map hab i) := sorry

/-- The bundled colimit inclusion reflects the order on each stage. -/
theorem colimit_inclusion_le_iff {a : δ} {i j : (D.obj a).index} :
    (D.colimit_inclusion a).embedding i ≤ (D.colimit_inclusion a).embedding j ↔ i ≤ j := sorry

/-- Canonical stage inclusions form a coherent cocone over the descended system. -/
theorem colimit_inclusion_comp {a b : δ} (hab : a ≤ b) :
    (D.map hab).comp (D.colimit_inclusion b) = D.colimit_inclusion a := sorry

/-- The canonical lower cocone of a directed stage diagram, using the descended direct-limit
system as its vertex. -/
noncomputable def colimit_cocone : DirectedPreorderSystem.StageDiagram.Cocone D where
  vertex := {
    index := D.index_preord
    directed := D.index_preord_directed
    diagram := D.colimit_system
  }
  leg := D.colimit_inclusion
  leg_comp := D.colimit_inclusion_comp

end DirectedPreorderSystem.StageDiagram

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
