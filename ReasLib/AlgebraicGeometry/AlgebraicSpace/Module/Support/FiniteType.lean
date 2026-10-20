module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ResidueFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.LocalGeneration

/-!
# Support of finite-type quasi-coherent modules

The support of a finite-type quasi-coherent module on an algebraic space is closed, is detected
by geometric residue-field fibers, and pulls back to the inverse image of the support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The support of a finite-type quasi-coherent module on an algebraic space is closed. -/
theorem isClosed_moduleSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : IsClosed (moduleSupport F) :=
  sorry

/-- At a geometric point, support membership for a finite-type quasi-coherent module is
equivalent to nonvanishing of its étale module stalk and of its residue-field fiber. -/
theorem mem_moduleSupport_tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (xbar : GeometricPoint X) :
    List.TFAE [xbar.image ∈ moduleSupport F, ¬ IsZero (stalkModuleCat xbar F),
      Nontrivial (fiber xbar F)] :=
  sorry

/-- A finite-type quasi-coherent `𝒪_X`-module is supported at the image of a geometric point
if and only if the residue-field fiber there is nontrivial. -/
theorem mem_moduleSupport_iff_nontrivial_fiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (xbar : GeometricPoint X) :
    xbar.image ∈ moduleSupport F ↔ Nontrivial (fiber xbar F) :=
  sorry

/-- The support of the pullback of a finite-type quasi-coherent module along any morphism of
algebraic spaces is the inverse image of its support. -/
theorem moduleSupport_pullback_eq_preimage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (f : Y ⟶ X) :
    moduleSupport ((pullback f).obj F) = Points.map f ⁻¹' moduleSupport F :=
  sorry

/-- A point supports the pullback of a finite-type quasi-coherent module if and only if its
image supports the original module. -/
theorem mem_moduleSupport_pullback_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (f : Y ⟶ X) (y : Points Y) :
    y ∈ moduleSupport ((pullback f).obj F) ↔ Points.map f y ∈ moduleSupport F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
