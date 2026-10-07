module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A scheme module is flat over the base in codimension zero when it is flat at every
generic point of every fibre. -/
def flatOverInCodimensionZero {X S : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ S) : Prop :=
  ∀ (s : S) (x : f.fiber s),
    x ∈ genericPoints (f.fiber s) → flatOverAt ℱ f ((f.fiberι s) x)

namespace flatOverInCodimensionZero

/-- Codimension-zero flatness gives flatness at a generic point of a chosen fibre. -/
theorem flatOverAt {X S : Scheme.{u}} {ℱ : X.Modules} {f : X ⟶ S}
    (h : flatOverInCodimensionZero ℱ f) (s : S) (x : f.fiber s)
    (hx : x ∈ genericPoints (f.fiber s)) :
    Scheme.Modules.flatOverAt ℱ f ((f.fiberι s) x) := sorry

/-- Flatness over the base implies flatness over the base in codimension zero. -/
theorem of_flatOver {X S : Scheme.{u}} {ℱ : X.Modules} {f : X ⟶ S}
    (h : Scheme.Modules.flatOver ℱ f) : flatOverInCodimensionZero ℱ f := sorry

end flatOverInCodimensionZero

end AlgebraicGeometry.Scheme.Modules
