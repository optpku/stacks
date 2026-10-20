module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

/-!
# Composition of quasi-projective scheme morphisms

Quasi-projective morphisms are closed under composition over a quasi-compact base.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The composite of quasi-projective scheme morphisms is quasi-projective when the target
scheme is quasi-compact. -/
theorem QuasiProjective.comp
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [CompactSpace S] (hf : QuasiProjective f) (hg : QuasiProjective g) :
    QuasiProjective (f ≫ g) := sorry

/-- The composite of quasi-projective scheme morphisms is quasi-projective when the target
admits an ample invertible module. -/
theorem QuasiProjective.comp_of_hasAmpleInvertibleModule
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (hS : Scheme.Modules.HasAmpleInvertibleModule S)
    (hf : QuasiProjective f) (hg : QuasiProjective g) :
    QuasiProjective (f ≫ g) := sorry

/-- A composite of quasi-projective scheme morphisms over a quasi-compact target carries the
canonical quasi-projective instance. -/
instance quasiProjective_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [CompactSpace S] [QuasiProjective f] [QuasiProjective g] :
    QuasiProjective (f ≫ g) :=
  QuasiProjective.comp inferInstance inferInstance

end AlgebraicGeometry
