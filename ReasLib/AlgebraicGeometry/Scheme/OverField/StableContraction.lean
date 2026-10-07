module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

universe u

@[expose] public section
namespace AlgebraicGeometry

/-- A stable contraction is a morphism whose target is proper, one-dimensional, and at worst
nodal, whose structure sheaf is preserved by pushforward and whose first higher direct image of
the source structure sheaf vanishes, while the target curve dualizing module is ample. -/
structure StableContraction {k : Type u} [Field k] {X Y : SchemeOverField k}
    (c : X ⟶ Y) : Prop where
  proper : IsProper Y.hom
  dimension : topologicalKrullDim Y.left = 1
  nodal : SchemeOverField.atWorstNodal Y
  structureSheaf : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom)
  firstDirectImage : IsZero (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
    (SheafOfModules.unit X.left.ringCatSheaf) 1)
  ample : Scheme.Modules.isAmpleObject (@curveDualizingModule k _ Y.left Y.hom proper)

/-- Construct a stable contraction from its six defining target, pushforward, cohomological, and
dualizing-module properties. -/
def StableContraction.ofProperties {k : Type u} [Field k] {X Y : SchemeOverField k}
    (c : X ⟶ Y) (proper : IsProper Y.hom) (dimension : topologicalKrullDim Y.left = 1)
    (nodal : SchemeOverField.atWorstNodal Y)
    (structureSheaf : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom))
    (firstDirectImage : IsZero (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf) 1))
    (ample : Scheme.Modules.isAmpleObject (@curveDualizingModule k _ Y.left Y.hom proper)) :
    StableContraction c :=
  { proper, dimension, nodal, structureSheaf, firstDirectImage, ample }

/-- The target of a stable contraction is proper, one-dimensional, and at worst nodal. -/
theorem StableContraction.target_spec {k : Type u} [Field k] {X Y : SchemeOverField k}
    {c : X ⟶ Y} (h : StableContraction c) :
    IsProper Y.hom ∧ topologicalKrullDim Y.left = 1 ∧ SchemeOverField.atWorstNodal Y := sorry

/-- A stable contraction preserves the structure sheaf and has vanishing first higher direct
image of the source structure sheaf. -/
theorem StableContraction.sheaf_spec {k : Type u} [Field k] {X Y : SchemeOverField k}
    {c : X ⟶ Y} (h : StableContraction c) :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom) ∧
      IsZero (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
        (SheafOfModules.unit X.left.ringCatSheaf) 1) := sorry

/-- The curve dualizing module of the target of a stable contraction is ample. -/
theorem StableContraction.ample_spec {k : Type u} [Field k] {X Y : SchemeOverField k}
    {c : X ⟶ Y} (h : StableContraction c) :
    Scheme.Modules.isAmpleObject (@curveDualizingModule k _ Y.left Y.hom h.proper) := sorry

/-- A proper at-worst-nodal one-dimensional scheme over a field with constant global functions and
genus at least two admits a stable contraction. -/
theorem stableModelContraction {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hXdim : topologicalKrullDim X.left = 1)
    (hXsections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (hXgenus : 2 ≤ SchemeOverField.genus X hXdim hXsections)
    (hXnodal : SchemeOverField.atWorstNodal X) :
    ∃ (Y : SchemeOverField k) (c : X ⟶ Y), StableContraction c := sorry

/-- Any two stable contractions from a proper at-worst-nodal one-dimensional scheme with constant
global functions and genus at least two are uniquely isomorphic over the source. -/
theorem stableModelContraction_unique {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hXdim : topologicalKrullDim X.left = 1)
    (hXsections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (hXgenus : 2 ≤ SchemeOverField.genus X hXdim hXsections)
    (hXnodal : SchemeOverField.atWorstNodal X)
    {Y₁ Y₂ : SchemeOverField k} {c₁ : X ⟶ Y₁} {c₂ : X ⟶ Y₂}
    (hc₁ : StableContraction c₁) (hc₂ : StableContraction c₂) :
    ∃! e : Y₁ ≅ Y₂, c₁ ≫ e.hom = c₂ := sorry

end AlgebraicGeometry
