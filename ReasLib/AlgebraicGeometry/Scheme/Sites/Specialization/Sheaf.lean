module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Specialization.Presheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Sheafifications and sheaf conditions for specialization presheaves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Specialization

/-- The canonical étale sheafification of the specialization-pair presheaf. -/
noncomputable def pairSheaf [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] :
    Sheaf etaleTopology AddCommGrpCat.{u} :=
  (presheafToSheaf etaleTopology AddCommGrpCat.{u}).obj pairPresheaf

/-- The canonical étale sheafification of the length-`n` specialization-chain presheaf. -/
noncomputable def chainSheaf (n : ℕ)
    [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] :
    Sheaf etaleTopology AddCommGrpCat.{u} :=
  (presheafToSheaf etaleTopology AddCommGrpCat.{u}).obj (chainPresheaf n)

/-- The underlying presheaf of the pair sheaf is the sheafification of the pair presheaf. -/
theorem pairSheaf_obj [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] :
    pairSheaf.obj = sheafify etaleTopology pairPresheaf := sorry

/-- The underlying presheaf of the chain sheaf is the sheafification of the chain presheaf. -/
theorem chainSheaf_obj (n : ℕ) [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] :
    (chainSheaf n).obj = sheafify etaleTopology (chainPresheaf n) := sorry

/-- The pair presheaf is separated for the big étale topology. -/
theorem pairPresheaf_isSeparated :
    Presheaf.IsSeparated etaleTopology pairPresheaf := sorry

/-- Every length-`n` chain presheaf is separated for the big étale topology. -/
theorem chainPresheaf_isSeparated (n : ℕ) :
    Presheaf.IsSeparated etaleTopology (chainPresheaf n) := sorry

/-- The pair presheaf does not satisfy the étale sheaf condition. -/
theorem pairPresheaf_not_isSheaf :
    ¬ Presheaf.IsSheaf etaleTopology pairPresheaf := sorry

/-- Every positive-length chain presheaf fails the étale sheaf condition. -/
theorem chainPresheaf_not_isSheaf (n : ℕ) (hn : 0 < n) :
    ¬ Presheaf.IsSheaf etaleTopology (chainPresheaf n) := sorry

/-- The pair sheaf, viewed as a presheaf, satisfies the fppf sheaf condition. -/
theorem pairSheaf_isSheaf_fppf
    [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] :
    Presheaf.IsSheaf fppfTopology pairSheaf.obj := sorry

/-- Every chain sheaf, viewed as a presheaf, satisfies the fppf sheaf condition. -/
theorem chainSheaf_isSheaf_fppf (n : ℕ)
    [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] :
    Presheaf.IsSheaf fppfTopology (chainSheaf n).obj := sorry

end AlgebraicGeometry.Scheme.Specialization
