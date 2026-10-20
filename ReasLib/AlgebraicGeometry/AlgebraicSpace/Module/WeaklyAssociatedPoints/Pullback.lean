module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberStalkDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Weakly associated points under pullback

Weakly associated points of a quasi-coherent module pull back along a morphism
of algebraic spaces at points where it is flat and its fibre local ring has
dimension zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme and a
quasi-coherent module `𝒢` on `Y`, a point `x` is weakly associated to the
pullback of `𝒢` if its image is weakly associated to `𝒢`, `f` is flat at `x`,
and the local ring of the fibre at `x` has dimension zero. -/
@[stacks 0CUA]
theorem mem_weakAss_pullback_of_flatAt_of_fiberStalkDimEqAt_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (𝒢 : Y.Modules)
    [𝒢.IsQuasicoherent] (x : Points X) (hflat : FlatAt f x)
    (hdim : FiberStalkDimEqAt f 0 x) (hy : Points.map f x ∈ 𝒢.weakAss) :
    x ∈ ((pullback f).obj 𝒢).weakAss :=
  sorry

/-- For a finite flat morphism `f : X ⟶ Y` of algebraic spaces over a scheme
and a quasi-coherent module `𝒢` on `Y`, a point `x` is weakly associated to
the pullback of `𝒢` if and only if its image is weakly associated to `𝒢`. -/
@[stacks 0CUT]
theorem mem_weakAss_pullback_iff_of_isFinite_of_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [Flat f] (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] (x : Points X) :
    x ∈ ((pullback f).obj 𝒢).weakAss ↔ Points.map f x ∈ 𝒢.weakAss :=
  sorry

/-- For an étale morphism `f : X ⟶ Y` of algebraic spaces over a scheme
and a quasi-coherent module `𝒢` on `Y`, a point `x` is weakly associated to
the pullback of `𝒢` if and only if its image is weakly associated to `𝒢`. -/
@[stacks 0CUU]
theorem mem_weakAss_pullback_iff_of_etale
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] (x : Points X) :
    x ∈ ((pullback f).obj 𝒢).weakAss ↔ Points.map f x ∈ 𝒢.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
