/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Types.Empty
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits Opposite TopCat

universe u v

/- Domain-style sampling for Remark 6.7.2:
- primary domain: sheaves on a topological space, evaluated on the empty open and on disjoint
  unions of opens;
- sampled owner API:
  `TopCat.Sheaf.isTerminalOfEmpty`,
  `TopCat.Sheaf.isProductOfDisjoint`,
  `Types.isTerminalEquivUnique`,
  `IsTerminal`;
- owner abstraction: the core/canonical owner for the empty-open clause is the terminal-object
  statement `TopCat.Sheaf.isTerminalOfEmpty`;
- primitive data: only the sheaf `F`;
- derived API: the `Type`-valued singleton-section reformulation, obtained from
  `Types.isTerminalEquivUnique`.

Source/core/bridge triage:
- `source-facing`: the remark that a sheaf has a final object of sections over the empty open, and
  that disjoint unions of opens give binary products of sections;
- `core/canonical`: `TopCat.Sheaf.isTerminalOfEmpty` and `TopCat.Sheaf.isProductOfDisjoint`;
- `bridge/view`: `TopCat.Sheaf.Type.emptySectionsUnique`, the `Type`-specialization of terminality.

The type-valued singleton-section consequence is a shared instance under
`TopCat.Sheaf.Type.emptySectionsUnique`; this source file only records its source-facing use. -/

/- Remark 6.7.2 (1): for any sheaf on a topological space, the sections over the empty open are a
final object in the target category. -/
@[stacks 006U "sections over the empty open form a final object"]
recall TopCat.Sheaf.isTerminalOfEmpty

section

variable {X : TopCat.{u}} (F : X.Sheaf (Type v))

/- Remark 6.7.2 (2): for a sheaf of types or sets, the sections over the empty open form a
singleton type. -/
@[stacks 006U "sections over the empty open form a singleton type"]
#check (inferInstance : Unique (F.obj.obj (op ⊥)))

end

/- Remark 6.7.2 (3): if `U` and `V` are disjoint opens, then the sheaf condition identifies the
sections on `U ⊔ V` as the binary product of the sections on `U` and on `V`. -/
@[stacks 006U "sections over a disjoint union form a binary product"]
recall TopCat.Sheaf.isProductOfDisjoint
