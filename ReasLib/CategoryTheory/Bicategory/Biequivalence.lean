/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.LocalProperties

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u w' v' u'

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type u'} [Bicategory.{w', v'} C]

/-!
The object-level equivalence owner determines the invariant image notion for a pseudofunctor.
Exposing that image as an `ObjectProperty`, instead of repeating its existential presentation
inside every consumer, allows its full subbicategory and equivalence-closure API to be reused.

A biequivalence then has two independent components: every induced hom functor is an equivalence,
and every target object lies in this essential image.
-/

/-- The essential image of a pseudofunctor consists of target objects equivalent to objects in
its strict objectwise image. -/
@[stacks 0040 "essential image of a pseudofunctor"]
def essImage (F : B ⥤ᵖ C) : ObjectProperty C :=
  fun c ↦ ∃ b : B, Nonempty (F.obj b ≌ c)

/-- A target object lies in the essential image exactly when it is equivalent to the image of a
source object. -/
theorem mem_essImage_iff (F : B ⥤ᵖ C) (c : C) :
    F.essImage c ↔ ∃ b : B, Nonempty (F.obj b ≌ c) := sorry
/- Proof strategy: unfold `essImage`; both sides are definitionally identical. -/

/-- A chosen source object witnessing membership in the essential image. This is the
bicategorical counterpart of `Functor.essImage.witness`. -/
noncomputable def essImage.witness (F : B ⥤ᵖ C) {c : C}
    (h : F.essImage c) : B :=
  h.choose

/-- The chosen equivalence from the image of `h.witness` to the target object. Consumers of
the choice should use this comparison rather than unfold `essImage.witness`. -/
noncomputable def essImage.getEquivalence (F : B ⥤ᵖ C) {c : C}
    (h : F.essImage c) : F.obj (h.witness F) ≌ c :=
  Classical.choice h.choose_spec

/-- The essential image is the equivalence closure of the strict objectwise image. This is the
bicategorical analogue of `Functor.isoClosure_eq_essImage`. -/
theorem equivalenceClosure_eq_essImage (F : B ⥤ᵖ C) :
    (ObjectProperty.ofObj F.obj).equivalenceClosure = F.essImage := sorry
/- Proof strategy: extensionality and `ObjectProperty.ofObj_iff` reduce both sides to an image
object and an equivalence; reverse that equivalence with `Bicategory.Equivalence.symm` to account
for the two conventional orientations. -/

/-- Every object in the strict objectwise image of a pseudofunctor belongs to its essential
image. -/
theorem obj_mem_essImage (F : B ⥤ᵖ C) (b : B) : F.essImage (F.obj b) := sorry
/- Proof strategy: use `b` as the witness and `Bicategory.Equivalence.id (F.obj b)` as its
identity equivalence. -/

/-- The essential image of a pseudofunctor is invariant under bicategorical equivalence of
target objects. -/
instance essImage.isClosedUnderEquivalences (F : B ⥤ᵖ C) :
    F.essImage.IsClosedUnderEquivalences := sorry
/- Proof strategy: rewrite with `equivalenceClosure_eq_essImage F` and use the generic
equivalence-closure instance. -/

/-- A pseudofunctor is essentially surjective when every target object lies in its essential
image. This is the bicategorical analogue of `Functor.EssSurj`. -/
@[stacks 0040 "essentially surjective pseudofunctor"]
class EssSurj (F : B ⥤ᵖ C) : Prop where
  /-- Every target object lies in the essential image. -/
  mem_essImage (c : C) : F.essImage c

/-- A chosen source object above a target object for an essentially surjective
pseudofunctor. -/
@[stacks 0040 "object preimage under an essentially surjective pseudofunctor"]
noncomputable def objPreimage (F : B ⥤ᵖ C) [F.EssSurj] (c : C) : B :=
  (EssSurj.mem_essImage (F := F) c).witness F

/-- The canonical chosen equivalence from the image of `F.objPreimage c` to `c`. -/
noncomputable def objPreimage.equivalence (F : B ⥤ᵖ C) [F.EssSurj] (c : C) :
    F.obj (F.objPreimage c) ≌ c :=
  (EssSurj.mem_essImage (F := F) c).getEquivalence F

/-- A pseudofunctor is a biequivalence when it is locally an equivalence and essentially
surjective on objects.

This is the invariant weak notion of equivalence between bicategories: it does not require a
chosen strict inverse object function or equality of composite pseudofunctors. -/
@[stacks 0040 "biequivalence of bicategories"]
class IsBiequivalence (F : B ⥤ᵖ C) extends F.IsLocallyEquivalence, F.EssSurj

attribute [instance] IsBiequivalence.toIsLocallyEquivalence IsBiequivalence.toEssSurj

/-- The identity pseudofunctor is essentially surjective. -/
instance id.essSurj : (Pseudofunctor.id B).EssSurj := sorry
/- Proof strategy: each object is represented by itself and the identity bicategorical
equivalence. -/

/-- The identity pseudofunctor is a biequivalence. -/
instance id.isBiequivalence : (Pseudofunctor.id B).IsBiequivalence := sorry
/- Proof strategy: combine the identity local-equivalence instance with `id.essSurj`. -/

universe w'' v'' u''

variable {D : Type u''} [Bicategory.{w'', v''} D]

/-- A composite of essentially surjective pseudofunctors is essentially surjective. -/
instance comp.essSurj (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) [F.EssSurj] [G.EssSurj] :
    (F.comp G).EssSurj := sorry
/- Proof strategy: choose a preimage under `G`, then one under `F`; map the first chosen
equivalence through `G` and compose it with the second chosen equivalence. -/

/-- A composite of biequivalences is a biequivalence. -/
instance comp.isBiequivalence (F : B ⥤ᵖ C) (G : C ⥤ᵖ D)
    [F.IsBiequivalence] [G.IsBiequivalence] :
    (F.comp G).IsBiequivalence := sorry
/- Proof strategy: combine the composition instances for local equivalence and essential
surjectivity. -/

end Pseudofunctor

end CategoryTheory
