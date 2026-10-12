/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection

@[expose] public section

open AlgebraicGeometry

universe u

/- Compatibility check that the generalized trace-section predicate is available to
existing Chapter 49 consumers. -/
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection :
  ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf),
    W.module.obj.sections → Prop)
