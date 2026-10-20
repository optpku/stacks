/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping cospan transformations

This leaf owns the concrete `1`-cell action of a pseudofunctor on a walking-cospan
transformation.  The three vertex maps and the two pasted comparison isomorphisms are kept
explicit; their projection equations are in `Map.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/- The walking-cospan action is the componentwise image of the three `1`-morphisms and the two
generating `2`-cell comparisons.  This is the source-facing 1-cell map of Tag 003O. -/
/-- Apply a pseudofunctor to a cospan transformation. Its vertex maps are mapped
componentwise, and its generating comparisons are conjugated by pseudofunctor composition
comparisons. -/
@[stacks 0040 "map a bicategorical cospan transformation by a pseudofunctor"]
def map (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    CospanTransform (P.map f) (P.map g) (P.map f') (P.map g') :=
  mk (P.map ψ.left) (P.map ψ.right) (P.map ψ.base)
    ((P.mapComp ψ.left f').symm ≪≫ P.map₂Iso ψ.leftIso ≪≫
      P.mapComp f ψ.base)
    ((P.mapComp ψ.right g').symm ≪≫ P.map₂Iso ψ.rightIso ≪≫
      P.mapComp g ψ.base)

/- Data and axiom audit (mathlib 4.32): `map` stores the three mapped vertex maps and the two
canonical pasted comparison isomorphisms.  Deferred content is confined to the coherence fields
of the strong transformation assembled by `mk`; no component or comparison is selected by a
placeholder. -/

end CategoryTheory.Bicategory.CospanTransform
