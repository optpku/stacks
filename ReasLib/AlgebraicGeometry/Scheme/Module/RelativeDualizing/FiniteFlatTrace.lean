/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.TraceComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.DerivedQCoh
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- The global section of a finite-flat relative dualizing sheaf characterized by the
universal trace condition on its affine finite/open presentations. -/
noncomputable def finiteFlatTraceSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf) : W.module.obj.sections :=
  Classical.choose (exists_traceSection f W)

/-- The chosen finite-flat trace section satisfies the trace-section predicate. -/
theorem finiteFlatTraceSection_spec {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf) :
    W.IsTraceSection (finiteFlatTraceSection f W) := sorry

/-- Every finite-flat trace section agrees with the chosen finite-flat trace section. -/
theorem finiteFlatTraceSection_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf) {τ : W.module.obj.sections}
    (hτ : W.IsTraceSection τ) :
    finiteFlatTraceSection f W = τ := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

namespace AlgebraicGeometry.Scheme.DerivedQCoh

open AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- The degree-zero section transported from the finite-flat trace section through a
relative-dualizing identification. -/
noncomputable def adjointTraceSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf)
    (hW : RingedSpace.ModuleDerived.cohomologySheaf
        ((finiteRightAdjoint f).obj (structureSheaf X)).obj 0 =
      W.module.obj) :
    (RingedSpace.ModuleDerived.cohomologySheaf
      ((finiteRightAdjoint f).obj (structureSheaf X)).obj 0).sections :=
  SheafOfModules.sectionsMap (eqToIso hW).inv (finiteFlatTraceSection f W)

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

open AlgebraicGeometry.Scheme.DerivedQCoh

/-- The transported finite-flat trace section satisfies the relative-dualizing trace
section predicate. -/
theorem adjointTraceSection_isTraceSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf)
    (hW : RingedSpace.ModuleDerived.cohomologySheaf
        ((finiteRightAdjoint f).obj (structureSheaf X)).obj 0 =
      W.module.obj) :
    W.IsTraceSection
      (SheafOfModules.sectionsMap (eqToIso hW).hom (adjointTraceSection f W hW)) := sorry

/-- The transported finite-flat trace section equals every relative-dualizing trace
section under the degree-zero identification. -/
theorem traceSection_eq_adjointTrace {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf)
    (hW : RingedSpace.ModuleDerived.cohomologySheaf
        ((finiteRightAdjoint f).obj (structureSheaf X)).obj 0 =
      W.module.obj)
    (τ : W.module.obj.sections) (hτ : W.IsTraceSection τ) :
    SheafOfModules.sectionsMap (eqToIso hW).hom (adjointTraceSection f W hW) = τ := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
