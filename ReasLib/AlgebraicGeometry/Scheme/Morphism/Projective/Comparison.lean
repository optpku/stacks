module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Factorization

/-!
# Comparisons between projective morphism properties

This file compares projective and quasi-projective morphism properties, including their
characterization by properness.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Every H-projective morphism is H-quasi-projective. -/
theorem HProjective.toHQuasiProjective
    {X S : Scheme.{u}} {f : X ⟶ S} (h : HProjective f) :
    HQuasiProjective f := sorry

/-- Every projective morphism is quasi-projective. -/
theorem Projective.toQuasiProjective
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : Projective f) :
    QuasiProjective f := sorry

/-- Projectivity canonically implies quasi-projectivity. -/
instance instQuasiProjectiveOfProjective
    {X S : Scheme.{u}} (f : X ⟶ S) [Projective f] :
    QuasiProjective f := Projective.toQuasiProjective inferInstance

/-- Over a quasi-compact, quasi-separated base, a morphism is projective exactly when it is
quasi-projective and proper. -/
@[stacks 0BCL]
theorem projective_iff_quasiProjective_and_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] :
    Projective f ↔ QuasiProjective f ∧ IsProper f := sorry

/-- Over a quasi-compact, quasi-separated base, a morphism is H-projective exactly when it is
H-quasi-projective and proper. -/
@[stacks 0BCL]
theorem hProjective_iff_hQuasiProjective_and_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] :
    HProjective f ↔ HQuasiProjective f ∧ IsProper f := sorry

end AlgebraicGeometry
