/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Presheaf
import StacksCheckRecall


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w u1

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C]

section

variable (F : C ⥤ Type u1) [F.Faithful] (ℱ : X.Presheaf C)

/- Domain-style sampling for Definition 6.5.2:
- primary domain: `C`-valued presheaves on a topological space and their underlying set-valued
  presheaves obtained from a functor `F : C ⥤ Type u1`;
- sampled owner declarations:
  `TopCat.Presheaf`,
  `Functor.comp`,
  `Functor.comp_obj`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`;
- owner abstraction: there is no separate source-facing owner beyond the presheaf `ℱ` itself; the
  underlying presheaf of sets is the derived composite `ℱ ⋙ F`, so this file should recall that
  canonical composition directly instead of introducing any wrapper or alias;
- primitive data versus derived API: the primitive data are exactly the `C`-valued presheaf `ℱ`
  and the functor `F`; the underlying set-valued presheaf itself is derived by `Functor.comp`, and
  its objectwise values and restriction maps are then read off by `Functor.comp_obj` and
  `Functor.comp_map`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project underlying presheaf of sets attached to `ℱ` via `F`;
- `core/canonical`: functor composition in the presheaf category;
- `bridge/view`: later sheaf-condition comparisons such as
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`.
-/
/-
The source assumes that `F` is faithful because it is the underlying-set functor of a category of
algebraic structures. The derived presheaf itself only uses canonical functor composition, so the
same expression remains meaningful without faithfulness; retaining `[F.Faithful]` here records the
exact source setup while reusing `Functor.comp` as the data owner.
-/
/- Definition 6.5.2: for a presheaf `ℱ` on a topological space `X` with values in `C` and a
faithful functor `F : C ⥤ Type u1`, the underlying presheaf of sets relative to `F` is canonically
the composite `ℱ ⋙ F`, with values `U ↦ F.obj (ℱ.obj U)`. -/
@[stacks 006O "underlying presheaf of sets by faithful functor composition"]
#check (ℱ ⋙ F)

end
