module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived stalks of module sheaves on ringed sites

An exact module-stalk functor acts on unbounded derived categories through the canonical
`Functor.mapDerivedCategory` construction.
-/

@[expose] public section

-- Local instance justification (defeq pin): moduleStalkFunctor has the commutative-ring-sheaf source presentation, and mapDerivedCategory must use the same named standard quotient as the displayed ModuleDerived source.
attribute [local instance] RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]

/-- The exact point-stalk functor on module sheaves, lifted canonically to unbounded derived
categories. -/
@[stacks 0DJJ "derived module stalk"]
noncomputable abbrev moduleStalkDerived
    (p : Point.{w} J) (O : Sheaf J CommRingCat.{w}) :
    RingedSite.Hom.ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ⥤
      DerivedCategory (ModuleCat.{w} (p.stalkCommRing O)) :=
  (p.moduleStalkFunctor O).mapDerivedCategory

end CategoryTheory.GrothendieckTopology.Point
