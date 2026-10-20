/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Subfunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.BigZariski.Subfunctor

universe u v w

section

variable (F : Scheme.{u}ᵒᵖ ⥤ Type v)

/- Definition 26.15.3 (1): the Zariski sheaf condition. -/
@[stacks 01JI] #check Presheaf.IsSheaf Scheme.zariskiTopology F

/- Definition 26.15.3 (2): a subfunctor of `F`. -/
@[stacks 01JI] #check Subfunctor F

end

section

variable (F : Scheme.{u}ᵒᵖ ⥤ Type v)
variable (H : Subfunctor F)

/- Definition 26.15.3 (3): Zariski-open subfunctors. -/
@[stacks 01JI] #check IsZariskiOpen H
#check RepresentsOpen H
#check RepresentsOpen.mem_iff
#check RepresentsOpen.mem_iff_existsUnique_lift
#check RepresentsOpen.preimage
#check IsZariskiOpen.representingOpen
#check IsZariskiOpen.representingOpen_spec
#check IsZariskiOpen.map_mem_iff
#check IsZariskiOpen.map_mem_iff_existsUnique_lift
#check IsZariskiOpen.representingOpen_ι_mem
#check IsZariskiOpen.representingOpen_map
#check RepresentsOpen.eq_representingOpen
#check IsZariskiOpen.representingOpen_eq

/- The existential source presentation is exactly `IsZariskiOpen`; `representingOpen` and its
specification are the reusable choice-encapsulated owner. -/

end

section

variable (F : Scheme.{u}ᵒᵖ ⥤ Type u)
variable (H : Subfunctor F)

/- Under the same-universe hypothesis used by mathlib's Yoneda functor, source-facing Zariski
openness agrees with the canonical relative open-immersion predicate. -/
@[stacks 01JI] #check IsOpenImmersion.presheaf H.ι
#check isZariskiOpen_iff_presheaf H

end

section

variable (F : Scheme.{u}ᵒᵖ ⥤ Type v)

variable {I : Type w} (K : I → Subfunctor F)

/- Definition 26.15.3 (4): an indexed Zariski cover by subfunctors. -/
@[stacks 01JI] #check IsZariskiCover K

/- `IsZariskiCover` itself records the indexed open cover from the source definition; the
locally-surjective comparison below is its canonical site-level bridge. -/

variable [Small.{v} I]

#check IsZariskiCover.sigmaDesc_isLocallySurjective

end
