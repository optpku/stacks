module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

#check (geometricStalk :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (sbar : Scheme.GeometricPoint S), AddCommGrpCat.{u})

#check (geometricStalk_isZero_iff_of_image_eq :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (sbar tbar : Scheme.GeometricPoint S) (himage : sbar.image = tbar.image),
    IsZero (geometricStalk F sbar) ↔ IsZero (geometricStalk F tbar))

#check (abelianSheafSupport :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}), Set S)

#check (mem_abelianSheafSupport_iff :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (s : S),
    s ∈ abelianSheafSupport F ↔
      ∃ sbar : Scheme.GeometricPoint S,
        sbar.image = s ∧ ¬ IsZero (geometricStalk F sbar))

#check (mem_abelianSheafSupport_iff_geometricStalk :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (sbar : Scheme.GeometricPoint S),
    sbar.image ∈ abelianSheafSupport F ↔ ¬ IsZero (geometricStalk F sbar))

#check (largestVanishingOpen :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)), U.left.Opens)

#check (largestVanishingOpen_spec :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)), vanishesOn F U σ (largestVanishingOpen F U σ))

#check (le_largestVanishingOpen :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (V : U.left.Opens),
    vanishesOn F U σ V → V ≤ largestVanishingOpen F U σ)

#check (abelianSheafSectionSupport :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)), TopologicalSpace.Closeds U.left)

#check (abelianSheafSectionSupport_def :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)),
    abelianSheafSectionSupport F U σ =
      TopologicalSpace.Opens.compl (largestVanishingOpen F U σ))

#check (mem_abelianSheafSectionSupport_iff :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (ū : Scheme.GeometricPoint U.left),
    ū.image ∈ abelianSheafSectionSupport F U σ ↔ geometricGerm U F σ ū ≠ 0)

end AlgebraicGeometry.Scheme.Etale
