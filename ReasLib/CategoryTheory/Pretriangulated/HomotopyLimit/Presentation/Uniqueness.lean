module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Iso.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Uniqueness of Homotopy-Limit Presentations

Homotopy-limit objects for a fixed sequential inverse system are unique up to isomorphism.  The
existence API in this leaf retains compatibility with the explicit product cones and every stage
projection, without selecting a public comparison isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.Hom

/-- The underlying map of a presentation morphism over an isomorphism-valued inverse-system
morphism is an isomorphism. -/
@[stacks 08TC "isomorphism induced by a homotopy-limit presentation morphism"]
instance homIsIso {K L : SequentialInverseSystem D} {f : K ⟶ L} [IsIso f]
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y} (φ : Hom f P Q) :
    IsIso φ.hom := sorry

end Presentation.Hom

/-- Two presentations of the same sequential inverse system admit a compatible presentation
isomorphism. -/
@[stacks 08TC "uniqueness of a homotopy-limit presentation"]
theorem Presentation.nonemptyIso {K : SequentialInverseSystem D} {X Y : D}
    (P : Presentation K X) (Q : Presentation K Y) :
    Nonempty (Presentation.Iso (Iso.refl K) P Q) := sorry

namespace IsOf

/-- Any two homotopy-limit objects of the same sequential inverse system are nonemptily
isomorphic. -/
@[stacks 08TC "uniqueness of a sequential homotopy limit"]
theorem nonemptyIso {K : SequentialInverseSystem D} {X Y : D}
    (hX : HomotopyLimit.IsOf K X) (hY : HomotopyLimit.IsOf K Y) :
    Nonempty (X ≅ Y) := sorry

end IsOf

end CategoryTheory.HomotopyLimit
