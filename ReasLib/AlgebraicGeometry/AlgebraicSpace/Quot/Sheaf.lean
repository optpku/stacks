module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.Fpqc

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The functor of finitely presented quasi-coherent quotients of `F`, flat
over the test scheme and with proper support, is a sheaf for the fpqc topology
on schemes over `B`. -/
theorem quot_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (quot f F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
