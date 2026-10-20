module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Homothety
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-! # Properties of relative dualizing objects over affine algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RelativeDualizing

/-- Over an affine target, the right adjoint of derived quasicoherent pushforward
along a proper flat finitely presented morphism sends the structure sheaf to a
relatively perfect derived module. -/
theorem isPerfectRelativeTo
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAffine Y] [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    ModuleDerived.IsPerfectRelativeTo f (a.obj (DerivedQCoh.structureSheaf Y)).obj := sorry

/-- Over an affine target, the derived pushforward of the right adjoint's value
on the structure sheaf has zero cohomology sheaves in positive degrees for a
proper flat finitely presented morphism. -/
theorem pushforward_cohomology_isZero_of_pos
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAffine Y] [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (i : ℤ) (hi : 0 < i) :
    IsZero (ModuleDerived.cohomologySheaf
      ((pushforwardCohomologyIn f).obj (a.obj (DerivedQCoh.structureSheaf Y))).obj i) := sorry

/-- Over an affine target, the scalar homothety of the right adjoint's value on
the structure sheaf is invertible for a proper flat finitely presented morphism. -/
theorem homothety_isIso
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAffine Y] [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    IsIso (ModuleDerived.InternalHom.homothety
      (a.obj (DerivedQCoh.structureSheaf Y)).obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RelativeDualizing
