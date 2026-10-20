module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ResidueFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.FiniteType

/-!
# Support of a finite-type quasi-coherent module on an algebraic space

A finite-type quasi-coherent `𝒪_X`-module has closed support on `|X|`. At a geometric point
the support criterion is equivalent to nonvanishing of the étale stalk and of the residue-field
fiber. Pullback along any morphism of algebraic spaces preserves finite type and pulls support
back along the induced map on points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 67.15.2. A finite-type quasi-coherent module has closed support; its support is
detected by geometric stalks and residue-field fibers and commutes with arbitrary pullback. -/
@[stacks 07TZ]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isClosed_moduleSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType], IsClosed (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X),
    List.TFAE [xbar.image ∈ moduleSupport F, ¬ IsZero (stalkModuleCat xbar F),
      Nontrivial (fiber xbar F)])

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_iff_nontrivial_fiber :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X),
    xbar.image ∈ moduleSupport F ↔ Nontrivial (fiber xbar F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pullback_isFiniteType :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) (F : X.Modules) [F.IsFiniteType],
    ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj F).IsFiniteType)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport_pullback_eq_preimage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (f : Y ⟶ X),
    moduleSupport ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj F) =
      AlgebraicGeometry.AlgebraicSpace.Points.map f ⁻¹' moduleSupport F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupport_pullback_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (f : Y ⟶ X) (y : AlgebraicGeometry.AlgebraicSpace.Points Y),
    y ∈ moduleSupport ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj F) ↔
      AlgebraicGeometry.AlgebraicSpace.Points.map f y ∈ moduleSupport F)
