/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice

/-!
# Product-slice right-vertical functor

This file owns the base comparison and the induced functor from a product slice to a
categorical self-pullback. Observable formulas are kept in `RightVertical.Computations`.
-/

@[expose] public section

universe vC vXS uC uXS

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace Limits.CategoricalPullback.ProductSlice

section RightVertical

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type uC} [Category.{vC} C] [Limits.HasBinaryProducts C]
variable {XS : Type uXS} [Category.{vXS} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

namespace RightVertical.Implementation

/-- Naturality of the componentwise base comparison between the two product-slice legs. -/
private theorem baseIsoNaturality
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    {c d : Over (Limits.prod U V)} (f : c ⟶ d) :
    (((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp).map f) ≫
        (eU.app ((Over.map Limits.prod.fst).obj d) ≪≫
          (eV.app ((Over.map Limits.prod.snd).obj d)).symm).hom =
      (eU.app ((Over.map Limits.prod.fst).obj c) ≪≫
          (eV.app ((Over.map Limits.prod.snd).obj c)).symm).hom ≫
        (((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp).map f) := sorry
/- Proof strategy: compose the naturality equations for `eU.hom` and `eV.inv`, then reassociate
composition. -/

end RightVertical.Implementation

/-- The base isomorphism showing that the two product-slice legs into `C` agree after applying the
representing isomorphisms `gU ⋙ xp ≅ C/U` and `gV ⋙ xp ≅ C/V`. -/
noncomputable def RightVertical.baseIso
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp) :=
  NatIso.ofComponents
    (fun c => eU.app ((Over.map Limits.prod.fst).obj c) ≪≫
      (eV.app ((Over.map Limits.prod.snd).obj c)).symm)
    (RightVertical.Implementation.baseIsoNaturality eU eV)

namespace RightVertical.Implementation

/-- The object of `xp ⊡ xp` determined by the two product-slice legs. -/
private noncomputable def object
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    (c : Over (Limits.prod U V)) : xp ⊡ xp where
  fst := gU.obj ((Over.map Limits.prod.fst).obj c)
  snd := gV.obj ((Over.map Limits.prod.snd).obj c)
  iso := eH.app c

/-- The two leg maps induced by a product-slice morphism respect the structural pullback
isomorphisms. -/
private theorem map_comm
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    {c d : Over (Limits.prod U V)} (f : c ⟶ d) :
    xp.map (gU.map ((Over.map Limits.prod.fst).map f)) ≫
        (object eH d).iso.hom =
      (object eH c).iso.hom ≫
        xp.map (gV.map ((Over.map Limits.prod.snd).map f)) := sorry
/- Proof strategy: this is `eH.hom.naturality f` after unfolding the two composite functors. -/

/-- The morphism of `xp ⊡ xp` induced by a product-slice morphism. -/
private noncomputable def map
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    {c d : Over (Limits.prod U V)} (f : c ⟶ d) :
    object eH c ⟶ object eH d where
  fst := gU.map ((Over.map Limits.prod.fst).map f)
  snd := gV.map ((Over.map Limits.prod.snd).map f)
  w := map_comm eH f

/-- The product-slice right-vertical map preserves identities. -/
private theorem map_id
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    (c : Over (Limits.prod U V)) :
    map eH (𝟙 c) = 𝟙 (object eH c) := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext` and use the identity laws of
`Over.map`, `gU`, and `gV`. -/

/-- The product-slice right-vertical map preserves composition. -/
private theorem map_comp
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    {c d e : Over (Limits.prod U V)} (f : c ⟶ d) (g : d ⟶ e) :
    map eH (f ≫ g) = map eH f ≫ map eH g := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext` and use the composition laws of
`Over.map`, `gU`, and `gV`. -/

end RightVertical.Implementation

/-- The canonical functor from the product slice `C/(U × V)` into `xp ⊡ xp` induced by the two
slice legs over `U` and `V`. -/
noncomputable def RightVertical.functor
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp)) :
    Over (Limits.prod U V) ⥤ xp ⊡ xp where
  obj := RightVertical.Implementation.object eH
  map := RightVertical.Implementation.map eH
  map_id := RightVertical.Implementation.map_id eH
  map_comp := RightVertical.Implementation.map_comp eH

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
