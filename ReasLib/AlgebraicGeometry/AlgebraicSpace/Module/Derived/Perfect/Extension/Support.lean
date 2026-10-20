module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a quasi-compact, quasi-separated algebraic space, a map from a perfect derived
module on a quasi-compact open subspace, supported over a closed subset whose complement
immersion is quasi-compact, extends from a globally perfect derived module supported on
that closed subset, with the original module a compatible retract of its restriction. -/
theorem exists_supported_retract_extension {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (W : OpenSubspace X)
    [IsQuasiCompact W.X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.fromOpens T.compl).ι) (E : DerivedQCoh X)
    (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P)
    (hP_support :
      ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
    (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj) :
    ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
      (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
      (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
      r.i ≫ (ModuleDerived.pullback W.ι).map β = α := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
