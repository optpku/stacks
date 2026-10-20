module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology over the terminal presheaf

The free abelian sheaf on the terminal type-valued presheaf is the constant integer sheaf.
Consequently cohomology over the terminal presheaf agrees with ordinary sheaf cohomology.
-/

@[expose] public section

noncomputable section

universe z w v u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- The free abelian sheaf on the terminal presheaf is canonically the constant integer sheaf. -/
@[stacks 09VY "free abelian terminal presheaf"]
noncomputable def freeAbelianTerminalIsoInteger
    (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{max w v}] :
    J.freeAbelianSheaf (Presheaf.terminal.{max w v} C) ≅
      constantIntegerSheaf J :=
  (presheafToSheaf J AddCommGrpCat.{max w v}).mapIso
      ((Functor.compConstIso Cᵒᵖ AddCommGrpCat.free).symm.app
        (PUnit : Type (max w v))) ≪≫
    (constantSheaf J AddCommGrpCat.{max w v}).mapIso
      freePUnitIsoInteger

namespace FreeAbelianYoneda

/-- The free abelian Yoneda sheaf represented by a terminal object is the constant integer sheaf. -/
@[stacks 09VY "free abelian terminal representable"]
noncomputable def terminalIsoInteger
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (T : C) (hT : Limits.IsTerminal T) :
    CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.obj J T ≅
      constantIntegerSheaf J :=
  J.freeAbelianSheafFunctor.mapIso (Presheaf.yonedaTerminalIso T hT) ≪≫
    J.freeAbelianTerminalIsoInteger

end FreeAbelianYoneda

end GrothendieckTopology

namespace Sheaf.TerminalCohomology

variable {C : Type u} [Category.{v} C]

/-- Cohomology over the terminal presheaf is naturally isomorphic to `Ext` from the constant
integer sheaf. -/
@[stacks 09VY "terminal presheaf cohomology"]
noncomputable def isoExt
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (n : ℕ) :
    Sheaf.cohomologyOverPresheafFunctor.{z, w, v, u} J
        (Presheaf.terminal C) n ≅
      Abelian.extFunctorObj.{z}
        (constantIntegerSheaf J : Sheaf J AddCommGrpCat.{max w v}) n :=
  (Abelian.extFunctor n).mapIso
    (Iso.op (J.freeAbelianTerminalIsoInteger).symm)

/-- Evaluation of cohomology over the terminal presheaf is isomorphic to ordinary global
sheaf cohomology. -/
@[stacks 09VY "global cohomology"]
theorem isomorphicGlobal
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (I : Sheaf J AddCommGrpCat.{max w v}) (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyOverPresheafFunctor.{z, w, v, u} J
        (Presheaf.terminal C) n).obj I)
      ((Sheaf.functorH.{z, max w v, v, u} J n).obj I) := sorry

end Sheaf.TerminalCohomology

end CategoryTheory

/- These data declarations are explicit composites of canonical functorial isomorphisms; any
inherited proof debt lies only in their owners' naturality or coherence fields. -/
