module

public import Mathlib.Topology.Sheaves.PUnit

/-!
# Sheaves on indiscrete spaces

On an indiscrete space, a morphism of sheaves is determined by its component on the top open.
This file packages the reconstruction and extensionality API for sheaves valued in an arbitrary
category with a terminal object.  Module sheaves have a richer linear version in
`Algebra.Category.ModuleCat.Sheaf.Indiscrete`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u v w

namespace TopCat.Sheaf.Indiscrete

variable {X : TopCat.{w}} [IndiscreteTopology X]
variable {C : Type u} [Category.{v} C] [HasTerminal C]

/-- The component on an open of a sheaf morphism reconstructed from its component on the top
open. -/
noncomputable def homOfTopApp (G H : TopCat.Sheaf C X)
    (t : G.obj.obj (op (⊤ : Opens X)) ⟶ H.obj.obj (op ⊤))
    (U : (Opens X)ᵒᵖ) : G.obj.obj U ⟶ H.obj.obj U :=
  @dite (G.obj.obj U ⟶ H.obj.obj U) (U = op (⊤ : Opens X))
    (Classical.propDecidable _)
    (fun hU ↦
      Eq.mp (congrArg (fun V ↦ G.obj.obj V ⟶ H.obj.obj V) hU).symm t)
    (fun hU ↦
      (H.isTerminalOfEqEmpty
        ((Opens.eq_bot_or_top (unop U)).resolve_right
          (fun h ↦ hU (congrArg op h)))).from (G.obj.obj U))

/-- The components reconstructed from the top open form a natural transformation. -/
theorem homOfTopApp_naturality (G H : TopCat.Sheaf C X)
    (t : G.obj.obj (op (⊤ : Opens X)) ⟶ H.obj.obj (op ⊤))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    G.obj.map i ≫ homOfTopApp G H t V = homOfTopApp G H t U ≫ H.obj.map i := sorry

/-- A morphism of sheaves on an indiscrete space reconstructed from its top-open component. -/
noncomputable def homOfTop (G H : TopCat.Sheaf C X)
    (t : G.obj.obj (op (⊤ : Opens X)) ⟶ H.obj.obj (op ⊤)) : G ⟶ H where
  hom :=
    { app := homOfTopApp G H t
      naturality := fun _ _ i ↦ homOfTopApp_naturality G H t i }

/-- Reconstruction has the prescribed component on the top open. -/
@[simp]
theorem homOfTop_app_top (G H : TopCat.Sheaf C X)
    (t : G.obj.obj (op (⊤ : Opens X)) ⟶ H.obj.obj (op ⊤)) :
    (homOfTop G H t).hom.app (op ⊤) = t := sorry

/-- Reconstructing a sheaf morphism from its top-open component recovers that morphism. -/
@[simp]
theorem homOfTop_app_top_leftInverse (G H : TopCat.Sheaf C X) (f : G ⟶ H) :
    homOfTop G H (f.hom.app (op (⊤ : Opens X))) = f := sorry

/-- Morphisms of sheaves on an indiscrete space are equivalent to morphisms between their
top-open values. -/
noncomputable def homEquivTop (G H : TopCat.Sheaf C X) :
    (G ⟶ H) ≃
      (G.obj.obj (op (⊤ : Opens X)) ⟶ H.obj.obj (op ⊤)) where
  toFun f := f.hom.app (op ⊤)
  invFun := homOfTop G H
  left_inv := homOfTop_app_top_leftInverse G H
  right_inv := homOfTop_app_top G H

/-- Two morphisms of sheaves on an indiscrete space agree when their top-open components agree. -/
@[ext]
theorem hom_ext_top {G H : TopCat.Sheaf C X} {f g : G ⟶ H}
    (h : f.hom.app (op (⊤ : Opens X)) = g.hom.app (op ⊤)) : f = g := sorry

/-- An isomorphism of top-open values extends canonically to an isomorphism of sheaves on an
indiscrete space. -/
noncomputable def isoOfTop (G H : TopCat.Sheaf C X)
    (e : G.obj.obj (op (⊤ : Opens X)) ≅ H.obj.obj (op ⊤)) : G ≅ H where
  hom := homOfTop G H e.hom
  inv := homOfTop H G e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `isoOfTop` on the top open is the supplied isomorphism. -/
@[simp]
theorem isoOfTop_hom_app_top (G H : TopCat.Sheaf C X)
    (e : G.obj.obj (op (⊤ : Opens X)) ≅ H.obj.obj (op ⊤)) :
    (isoOfTop G H e).hom.hom.app (op ⊤) = e.hom := sorry

/-- The inverse component of `isoOfTop` on the top open is the supplied isomorphism. -/
@[simp]
theorem isoOfTop_inv_app_top (G H : TopCat.Sheaf C X)
    (e : G.obj.obj (op (⊤ : Opens X)) ≅ H.obj.obj (op ⊤)) :
    (isoOfTop G H e).inv.hom.app (op ⊤) = e.inv := sorry

end TopCat.Sheaf.Indiscrete
