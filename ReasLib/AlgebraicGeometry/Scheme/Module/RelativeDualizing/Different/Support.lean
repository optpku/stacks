/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- The support of the different of a flat quasi-finite morphism of Noetherian schemes is
the locus where the morphism is not unramified. -/
theorem different_support_eq_nonUnramifiedAtLocus
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ) :
    ((W.different τ).support : Set Y) = {y : Y | ¬ f.UnramifiedAt y} := sorry

/-- The support of the different of a flat quasi-finite morphism of Noetherian schemes is
the locus where the morphism is not étale. -/
theorem different_support_eq_nonEtaleAtLocus
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ) :
    ((W.different τ).support : Set Y) = {y : Y | ¬ f.EtaleAt y} := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
