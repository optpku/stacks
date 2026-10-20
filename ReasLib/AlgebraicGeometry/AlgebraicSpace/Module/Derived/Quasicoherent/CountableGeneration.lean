module

public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.CountableGeneration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a quasi-compact and absolutely quasi-separated algebraic space over a scheme with
countable structure rings on every affine étale chart, a derived quasicoherent module is a
sequential homotopy colimit of perfect derived modules if and only if every cohomology sheaf
has countable sections on every affine étale chart. -/
theorem perfectHomotopyColimit_iff_countableAffineEtaleSections
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : ∀ U : affineEtaleSite X, Countable (structureRing U.obj))
    (K : DerivedQCoh X) :
    sequentialHomotopyColimits
      (fun E : ModuleDerived X ↦ ModuleDerived.IsPerfect E) K.obj ↔
      ∀ i : ℤ, ∀ U : affineEtaleSite X,
        Countable
          (sectionModule ((DerivedCategory.homologyFunctor (Modules X) i).obj K.obj) U.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
