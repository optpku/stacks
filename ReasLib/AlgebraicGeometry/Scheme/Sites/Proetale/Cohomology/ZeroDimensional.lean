module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ZeroDimensional

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Constant-coefficient first pro-étale cohomology vanishes on an affine scheme
whose points are closed and whose residue fields are separably closed. -/
theorem proEtH1_constant_isZero (Y : Scheme.{u}) [IsAffine Y]
    (h_closed : ∀ y : Y, IsClosed ({y} : Set Y))
    (h_res : ∀ y : Y, IsSepClosed (Y.residueField y))
    (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (topology Y) AddCommGrpCat.{u + 1})] :
    IsZero ((Sheaf.functorH (topology Y) 1).obj
      ((constantSheaf (topology Y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A))) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
