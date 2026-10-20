module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

/-- The constant sheaf associated to a torsion abelian group is locally torsion on any site. -/
theorem constantSheaf_isLocallyTorsion {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    (A : AddCommGrpCat.{w}) (hA : AddMonoid.IsTorsion A) :
    ((constantSheaf J AddCommGrpCat.{w}).obj A).IsLocallyTorsion := sorry

end CategoryTheory.Sheaf

end

end
