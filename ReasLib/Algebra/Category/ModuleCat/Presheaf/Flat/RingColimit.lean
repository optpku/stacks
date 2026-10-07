module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.Flat.Tensor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat modules over colimits of rings

@stack 05UU

This file relates stagewise flatness for a cofiltered diagram of commutative rings to flatness over
its colimit.  The smallness data required by the presheaf colimit functor is an explicit categorical
hypothesis rather than a locally manufactured instance.
-/

open CategoryTheory Limits

universe u

noncomputable section

namespace PresheafOfModules.RingColimit

variable {C : Type u} [Category.{u} C] [LocallySmall.{u} C]
variable [IsCofiltered C] [InitiallySmall.{u} C]

/-- Lemma 10.39.6 (1): a module over a cofiltered colimit of rings is flat when its restriction to
every stage is flat. -/
@[stacks 05UU "(1), stagewise restriction criterion"]
theorem flat_of_stagewise_restrictScalars
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : ModuleCat.{u} (colimit R : CommRingCat))
    [∀ U, Module.Flat (R.obj U)
      ((ModuleCat.restrictScalars ((colimit.cocone R).ι.app U).hom).obj M)] :
    Module.Flat (colimit R : CommRingCat) M := sorry

/-- Lemma 10.39.6 (2): the colimit of a compatible system of stagewise flat modules is flat over
the colimit ring. -/
@[stacks 05UU "(2), colimit of stagewise flat modules"]
theorem flat_colimitFunctor_of_stagewise_flat
    (R : Cᵒᵖ ⥤ CommRingCat)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    [∀ U, Module.Flat (R.obj U) (M.obj U)] :
    Module.Flat (colimit R : CommRingCat)
      ((ModuleCat.restrictScalars
          (preservesColimitIso (forget₂ CommRingCat RingCat) R).hom.hom).obj
        ((colimitFunctor.{u}
          (colimit.isColimit (R ⋙ forget₂ CommRingCat RingCat))).obj M)) := sorry

end PresheafOfModules.RingColimit
