module

public import Mathlib.Tactic.Recall
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (ℱ : Cᵒᵖ ⥤ Type w)

/- Domain-style sampling for 21.2.0.2:
- primary domain: set-valued presheaves and their global sections;
- sampled owner API:
  `Functor.sections`,
  `Functor.sectionsEquivHom`,
  `Presheaf.terminal`,
  `Presheaf.terminalIsTerminal`;
- best owner abstraction: the core owner is `Functor.sections`, and the source-facing
  `ℱ.sections ≃ (Presheaf.terminal C ⟶ ℱ)` formula is its canonical bridge
  `Functor.sectionsEquivHom`;
- primitive data: only the presheaf `ℱ : Cᵒᵖ ⥤ Type w`;
- derived API: the canonical `Presheaf.terminal C` and the induced
  equivalence from global sections to morphisms out of that terminal object.

Source/core/bridge triage:
- `source-facing`: the identification of global sections with morphisms from the terminal
  presheaf;
- `core/canonical`: `Functor.sections`;
- `bridge/view`: `Functor.sectionsEquivHom`, together with `Presheaf.terminalIsTerminal`.

This item is therefore a bridge/view recall, not a new owner declaration. -/
/- 21.2.0.2: for a set-valued presheaf `ℱ : Cᵒᵖ ⥤ Type w`, the identification
`ℱ.sections ≃ (Presheaf.terminal C ⟶ ℱ)` is the canonical bridge
`Functor.sectionsEquivHom`. -/
@[stacks 071D "global sections as maps from the terminal presheaf"]
#check @Functor.sectionsEquivHom

/- Companion check: `Presheaf.terminal C` is the singleton-valued constant presheaf and is terminal
in `Cᵒᵖ ⥤ Type w`. -/
@[stacks 071D "terminal presheaf"]
#check @Presheaf.terminalIsTerminal

/- Source-facing specialization: global sections of `ℱ` identify with morphisms from the terminal
presheaf to `ℱ`. -/
@[stacks 071D "global-sections source-facing equivalence"]
#check
  (ℱ.sectionsEquivHom PUnit : ℱ.sections ≃ (Presheaf.terminal C ⟶ ℱ))

end CategoryTheory
