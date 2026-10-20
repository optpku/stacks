/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.Functoriality
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Component
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialObject

variable (X Y : SimplicialObject TopCat.{u}) (f : Y ⟶ X) (n : ℕ)
variable [HasWeakSheafify (zariskiTopology X) (Type u)]
variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
variable [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
  (Opens.map (f.app (op ⦋n⦌))).op.HasLeftKanExtension P]
variable [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
  (component X n).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
  (component Y n).op.HasPointwiseRightKanExtension F]
variable [PreservesFiniteLimits
  ((zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y))]
variable [PreservesFiniteLimits
  ((Opens.map (f.app (op ⦋n⦌))).sheafPullback (Type u)
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))))]

/- Lemma 85.2.7: a morphism `f : Y ⟶ X` of simplicial spaces induces a commutative
diagram of topoi `Sh(Y_n) ⟶ Sh(X_n)` over `Sh(Y_Zar) ⟶ Sh(X_Zar)`.
The horizontal inverse images are the canonical sheaf pullbacks along `zariskiMap f`
and `f.app (op ⦋n⦌)`. The component inverse images are canonically identified with
`sheafFiber X (op ⦋n⦌) (Type u)` (definitionally `sheafComponent X n (Type u)`) by
`componentMorphism_inverseImage_iso_sheafComponent`, so the
following natural isomorphism expresses commutativity of the inverse-image square. -/
@[stacks 09W2] #check
  (CategoryTheory.SimplicialObject.zariskiMap_pullbackRestrict f (op ⦋n⦌) :
    (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
      sheafFiber Y (op ⦋n⦌) (Type u) ≅
    sheafFiber X (op ⦋n⦌) (Type u) ⋙ TopCat.Sheaf.pullback (Type u) (f.app (op ⦋n⦌)))

end CategoryTheory.SimplicialObject
