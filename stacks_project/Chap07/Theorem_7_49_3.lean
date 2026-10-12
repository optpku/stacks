/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.TypeSheafification

@[expose] public section

/- Domain-style sampling for Theorem 7.49.3:
- primary domain: the plus construction and sheafification for set-valued presheaves on a
  Grothendieck site;
- sampled owner API:
  `GrothendieckTopology.plusObj_isSeparated`,
  `GrothendieckTopology.plusObj_isSheaf_of_isSeparated`,
  `GrothendieckTopology.toPlus_injective_of_isSeparated`,
  `GrothendieckTopology.isIso_toPlus_of_isSheaf`,
  `GrothendieckTopology.Plus.isSheaf_plus_plus`;
- source-facing layer: the textbook assertions about `L F`, `F ⟶ L F`, and `L (L F)`;
- core/canonical owner: the plus-construction/sheafification API on `GrothendieckTopology`;
- bridge/view: the monomorphism reformulation `GrothendieckTopology.toPlus_mono_of_isSeparated`, obtained from the
  source-facing objectwise injectivity statement through `Presheaf.mono_iff_injective`.

Primitive data are only the site `J` and the presheaf `F`. The map `J.toPlus F`, the iterated plus
object, and sheafification are canonical constructions of the Grothendieck-topology owner, so this
file should recall those owners directly rather than keep parallel restatements.
-/

open CategoryTheory Opposite
open GrothendieckTopology

universe u v

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))

/- Theorem 7.49.3 (1): the plus construction `L F` is separated. This is the same statement as
Theorem 7.10.10 (1), already recorded in the chapter API. -/
@[stacks 00ZJ] #check GrothendieckTopology.plusObj_isSeparated J F

/- Theorem 7.49.3 (2), first assertion: if `F` is separated, then `L F` is a sheaf. This is the
same statement as Theorem 7.10.10 (2), first assertion. -/
@[stacks 00ZJ "(2) sheaf"] #check GrothendieckTopology.plusObj_isSheaf_of_isSeparated J F

/- Theorem 7.49.3 (2), second assertion: if `F` is separated, then the canonical map
`F ⟶ L F` is injective on sections over every object. This is the same statement as
Theorem 7.10.10 (2), second assertion. -/
@[stacks 00ZJ "(2) injective"] #check GrothendieckTopology.toPlus_injective_of_isSeparated J F

/- Companion bridge for Theorem 7.49.3 (2), second assertion: via Definition 7.3.1 and
Lemma 7.3.2, the same map is a monomorphism. -/
#check GrothendieckTopology.toPlus_mono_of_isSeparated J F

/- Theorem 7.49.3 (3): if `F` is a sheaf, then the canonical map `F ⟶ L F` is an isomorphism.
This is the same statement as Theorem 7.10.10 (3), now exposed by direct recall of the canonical
owner theorem. -/
@[stacks 00ZJ "(3)"] #check @isIso_toPlus_of_isSheaf

/- Theorem 7.49.3 (4): the iterated plus construction `L (L F)` is a sheaf. This is the same
statement as Theorem 7.10.10 (4), now exposed by direct recall of the canonical owner theorem. -/
@[stacks 00ZJ "(4)"] #check @Plus.isSheaf_plus_plus

/- Definition 7.49.4 (00ZL): the associated sheaf is the explicit double-plus construction. -/
@[stacks 00ZL "associated sheaf as double plus"]
#check (J.plusObj (J.plusObj F) : Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.49.4 (00ZL): its canonical map is the composite of the two `toPlus` maps. -/
@[stacks 00ZL "double-plus canonical map"]
#check (J.toPlus F ≫ J.toPlus (J.plusObj F))

/- Companion reformulation of Theorem 7.49.3 (4): since `J.sheafify F = F⁺⁺`,
the sheafification `J.sheafify F` is a sheaf. The canonical library-facing companion is the
theorem `sheafify_isSheaf`. -/
#check @sheafify_isSheaf

end
