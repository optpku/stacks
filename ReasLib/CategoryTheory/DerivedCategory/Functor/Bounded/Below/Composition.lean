module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic

/-!
# Composition of bounded-below induced functors

The bounded-below functor induced by a composite agrees with the two-stage functor obtained by
mapping the homotopy category first and then applying the second bounded-below induced functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.toBoundedBelowDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Abelian 𝒞]
  [HasDerivedCategory.{w} 𝒞]

/-- The two-stage functor `K⁺(𝒜) ⥤ D⁺(𝒞)` obtained by first applying an additive functor
`F : 𝒜 ⥤ ℬ`, then applying `G : ℬ ⥤ 𝒞`, and finally passing to `D⁺(𝒞)`. -/
@[stacks 05T4 "two-stage bounded-below derived functor"]
def comp (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞)
    [F.Additive] [G.Additive] :
    HomotopyCategory.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒞 :=
  F.mapHomotopyCategoryPlus ⋙ G.toBoundedBelowDerived

/-- If `H : 𝒜 ⥤ 𝒞` is isomorphic to `F ⋙ G`, the bounded-below functor induced by `H` is
canonically isomorphic to the two-stage functor induced by `F` and `G`. -/
@[stacks 05T4 "bounded-below composition comparison from an underived isomorphism"]
noncomputable def compIsoOfIso
    (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) {H : 𝒜 ⥤ 𝒞}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G) :
    H.toBoundedBelowDerived ≅ comp F G :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso hcomp.symm).symm
      (DerivedCategory.Plus.Qh :
        HomotopyCategory.Plus 𝒞 ⥤ DerivedCategory.Plus 𝒞) ≪≫
    Functor.associator F.mapHomotopyCategoryPlus G.mapHomotopyCategoryPlus
      (DerivedCategory.Plus.Qh :
        HomotopyCategory.Plus 𝒞 ⥤ DerivedCategory.Plus 𝒞)

/-- The forward component of the bounded-below composition comparison is localization of
the inverse homotopy-category comparison. -/
@[simp]
theorem compIsoOfIso_hom_app
    (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) {H : 𝒜 ⥤ 𝒞}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    (X : HomotopyCategory.Plus 𝒜) :
    (compIsoOfIso F G hcomp).hom.app X =
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso hcomp.symm).inv.app X) := sorry

/-- The inverse component of the bounded-below composition comparison is localization of
the forward homotopy-category comparison. -/
@[simp]
theorem compIsoOfIso_inv_app
    (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) {H : 𝒜 ⥤ 𝒞}
    [F.Additive] [G.Additive] [H.Additive] (hcomp : H ≅ F ⋙ G)
    (X : HomotopyCategory.Plus 𝒜) :
    (compIsoOfIso F G hcomp).inv.app X =
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso hcomp.symm).hom.app X) := sorry

/-- The bounded-below functor induced by `F ⋙ G` is canonically isomorphic to the two-stage
functor induced by `F` and `G`. -/
@[stacks 05T4 "bounded-below composition comparison"]
noncomputable def compIso
    (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) [F.Additive] [G.Additive] :
    (F ⋙ G).toBoundedBelowDerived ≅ comp F G :=
  compIsoOfIso F G (Iso.refl (F ⋙ G))

end CategoryTheory.Functor.toBoundedBelowDerived
