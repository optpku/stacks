module

public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of projective-object preservation

Projective-object preservation is invariant under natural isomorphism. This supplies the missing
transport needed to recognize precomposition along a composite from the two factor instances.
-/

@[expose] public section

open CategoryTheory

universe u v u' v' u'' v'' e ve

namespace CategoryTheory.Functor

/-- Projective-object preservation transports across a natural isomorphism of functors. -/
@[stacks 08PH "projective preservation under natural isomorphism"]
theorem preservesProjectiveObjects_of_iso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (e : F ≅ G) [F.PreservesProjectiveObjects] :
    G.PreservesProjectiveObjects := sorry

/-- Precomposition along a composite functor preserves projectives when each factor does. -/
@[stacks 08PH "projective preservation for composite precomposition"]
instance preservesProjectiveObjects_whiskering_comp
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] {E : Type e} [Category.{ve} E]
    (u : C' ⥤ C) (v : C'' ⥤ C')
    [((whiskeringLeft C'ᵒᵖ Cᵒᵖ E).obj u.op).PreservesProjectiveObjects]
    [((whiskeringLeft C''ᵒᵖ C'ᵒᵖ E).obj v.op).PreservesProjectiveObjects] :
    ((whiskeringLeft C''ᵒᵖ Cᵒᵖ E).obj (v ⋙ u).op).PreservesProjectiveObjects := sorry

end CategoryTheory.Functor
