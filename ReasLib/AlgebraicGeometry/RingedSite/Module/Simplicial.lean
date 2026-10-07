module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.CategoryTheory.Sites.Simplicial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules over simplicial ring sheaves

A simplicial sheaf of commutative rings on a site determines a sheaf of rings on the simplicial
site and hence a canonical category of module sheaves.  These are library owners rather than
Chapter 21 presentation artifacts.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Uncurrying degree and site variables gives the ring-presheaf functor on the simplicial site. -/
@[stacks 09D1 "associated simplicial ring presheaf functor"]
def ringPresheafFunctor :
    SimplicialObject (Sheaf J CommRingCat.{w}) ⥤
      ((SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{w}) :=
  presheafFunctor J CommRingCat.{w}

/-- The ring-valued presheaf on the simplicial site associated to a simplicial ring sheaf. -/
@[stacks 09D1 "associated simplicial ring presheaf"]
abbrev ringPresheaf (A : SimplicialObject (Sheaf J CommRingCat.{w})) :=
  (ringPresheafFunctor (J := J)).obj A

/-- A map of simplicial ring sheaves induces a map of their associated ring presheaves. -/
@[stacks 09D1 "associated simplicial ring presheaf map"]
abbrev ringPresheafMap
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})} (α : A ⟶ B) :
    ringPresheaf A ⟶ ringPresheaf B :=
  (ringPresheafFunctor (J := J)).map α

/-- Directly bundling the associated presheaf gives a functor to ring sheaves on the simplicial
site. -/
@[stacks 09D1 "associated simplicial ring sheaf functor"]
def ringSheafFunctor :
    SimplicialObject (Sheaf J CommRingCat.{w}) ⥤
      Sheaf (topology J) CommRingCat.{w} :=
  sheafFunctor J CommRingCat.{w}

/-- The sheaf of commutative rings on the simplicial site associated to `A`. -/
@[stacks 09D1 "associated simplicial ring sheaf"]
abbrev ringSheaf (A : SimplicialObject (Sheaf J CommRingCat.{w})) :=
  (ringSheafFunctor (J := J)).obj A

/-- The map of associated ring sheaves induced by a map of simplicial ring sheaves. -/
@[stacks 09D1 "associated simplicial ring sheaf map"]
abbrev ringSheafMap
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})} (α : A ⟶ B) :
    ringSheaf A ⟶ ringSheaf B :=
  (ringSheafFunctor (J := J)).map α

/-- Forgetting the bundled associated ring sheaf recovers its uncurried ring presheaf. -/
@[stacks 09D1 "underlying associated simplicial ring presheaf", simp]
theorem ringSheaf_val (A : SimplicialObject (Sheaf J CommRingCat.{w})) :
    (ringSheaf A).1 = ringPresheaf A := sorry

/-- Forgetting an associated ring-sheaf map recovers the uncurried presheaf map. -/
@[stacks 09D1 "underlying associated simplicial ring sheaf map", simp]
theorem ringSheafMap_val
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})} (α : A ⟶ B) :
    (ringSheafMap α).1 = ringPresheafMap α := sorry

/-- The category of module sheaves over a simplicial sheaf of commutative rings. -/
@[stacks 09D1 "simplicial module category"]
abbrev ModuleCat.{z}
    [GrothendieckTopology.HasSheafCompose (topology J)
      (forget₂ CommRingCat.{w} RingCat.{w})]
    (A : SimplicialObject (Sheaf J CommRingCat.{w})) :=
  SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, z, w}
    (topology J) (ringSheaf A)

set_option quotPrecheck false in
scoped[SimplicialSite] notation:max "Mod(" A:arg "•)" =>
  CategoryTheory.SimplicialSite.ModuleCat A

/-- The structure sheaf, viewed as the unit module on the simplicial site. -/
@[stacks 09D1 "simplicial unit module"]
abbrev unitModule
    [GrothendieckTopology.HasSheafCompose (topology J)
      (forget₂ CommRingCat.{w} RingCat.{w})]
    (A : SimplicialObject (Sheaf J CommRingCat.{w})) :
    ModuleCat (J := J) A :=
  _root_.SheafOfModules.RingedSite.unitModule (topology J) (ringSheaf A)

end CategoryTheory.SimplicialSite
