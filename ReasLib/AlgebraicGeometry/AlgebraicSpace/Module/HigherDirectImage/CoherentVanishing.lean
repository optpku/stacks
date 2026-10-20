/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension

/-!
# Coherent higher direct image stalk vanishing

Higher direct images of a coherent module along a proper morphism of algebraic
spaces with locally Noetherian target have vanishing geometric stalks in degrees
above the dimension of the geometric fibre. In particular, positive degrees
vanish whenever the geometric fibre is discrete.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.FormalFunctions

/-- Let `S` be a scheme and `f : X ⟶ Y` a proper morphism of algebraic spaces
over `S`, with `Y` locally Noetherian. If the geometric fibre `fiber f ybar` at
a geometric point `ybar` has discrete space of points, then for any coherent
sheaf `F` on `X`, the geometric stalk
`stalkModuleCat ybar (higherDirectImage f F p)` is zero for all `p > 0`. -/
@[stacks 0A4S]
theorem stalkModuleCat_higherDirectImage_isZero_of_discreteFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (F : X.Modules) [F.IsCoherent] (ybar : GeometricPoint Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules]
    (h_discrete : DiscreteTopology (Points (fiber f ybar)))
    (p : ℕ) (hp : 0 < p) :
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)) :=
  sorry

/-- For a proper morphism of algebraic spaces with locally Noetherian target, if the
geometric fibre at `ybar` has dimension `d`, then the geometric stalk of the higher
direct image of any coherent module vanishes in every degree greater than `d`. -/
@[stacks 0A4T]
theorem stalkModuleCat_isZero_of_proper_of_fiberDimension_eq
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ybar : GeometricPoint Y) (d : ℕ)
    (hdim : dimension (fiber f ybar) = (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] {p : ℕ} (hp : d < p) :
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)) :=
  sorry

/-- For a proper morphism of algebraic spaces with locally Noetherian target, the
geometric stalk of a coherent higher direct image vanishes whenever its degree is
strictly greater than the dimension of the geometric fibre, including an empty fibre. -/
theorem stalkModuleCat_isZero_of_lt_fiberDimension
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ybar : GeometricPoint Y) (F : X.Modules) [F.IsCoherent]
    {p : ℕ} (hp : dimension (fiber f ybar) < p) :
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalFunctions
