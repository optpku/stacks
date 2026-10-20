/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_71_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

/- Lemma 59.71.4 (1): constructibility of a sheaf of sets on `Xₑₜ` can be checked on a
Zariski open cover of `X`. -/
@[stacks 095F]
#check (CategoryTheory.Sheaf.isConstructibleEtale_iff_exists_openCover :
    ∀ {X : Scheme.{u}}
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology (Type (u + 1))),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F)))
    (h_finiteLocallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z)
        (F : Sheaf Z.smallEtaleTopology (Type (u + 1))),
        finiteLocallyConstant F → finiteLocallyConstant (restrict f F))
    (h_finiteLocallyConstant_iso :
      ∀ {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology (Type (u + 1))},
        Nonempty (F ≅ G) → finiteLocallyConstant F → finiteLocallyConstant G)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
    IsConstructibleEtaleSet (fun {Y} f ↦ restrict f) finiteLocallyConstant F ↔
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtaleSet (fun {Y} f ↦ restrict f) finiteLocallyConstant
            (restrict (𝒰.f i) F))

/- Lemma 59.71.4 (2): constructibility of a sheaf of abelian groups on `Xₑₜ` can be checked
on a Zariski open cover of `X`. -/
@[stacks 095F]
#check (CategoryTheory.Sheaf.isConstructibleEtale_iff_exists_openCover :
    ∀ {X : Scheme.{u}}
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F)))
    (h_finiteLocallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z)
        (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}),
        finiteLocallyConstant F → finiteLocallyConstant (restrict f F))
    (h_finiteLocallyConstant_iso :
      ∀ {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}},
        Nonempty (F ≅ G) → finiteLocallyConstant F → finiteLocallyConstant G)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    IsConstructibleEtaleAddCommGrp (fun {Y} f ↦ restrict f) finiteLocallyConstant F ↔
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtaleAddCommGrp (fun {Y} f ↦ restrict f) finiteLocallyConstant
            (restrict (𝒰.f i) F))

/- Lemma 59.71.4 (3): for a Noetherian ring `Λ`, constructibility of a sheaf of `Λ`-modules
on `Xₑₜ` can be checked on a Zariski open cover of `X`. -/
@[stacks 095F]
#check (CategoryTheory.Sheaf.isConstructibleEtale_iff_exists_openCover :
    ∀ {X : Scheme.{u}}
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology (ModuleCat.{w} Λ)),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F)))
    (h_finiteTypeLocallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z)
        (F : Sheaf Z.smallEtaleTopology (ModuleCat.{w} Λ)),
        finiteTypeLocallyConstant F → finiteTypeLocallyConstant (restrict f F))
    (h_finiteTypeLocallyConstant_iso :
      ∀ {Y : Scheme.{u}}
        {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)},
        Nonempty (F ≅ G) → finiteTypeLocallyConstant F → finiteTypeLocallyConstant G)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
    IsConstructibleEtaleModule (fun {Y} f ↦ restrict f) finiteTypeLocallyConstant F ↔
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtaleModule (fun {Y} f ↦ restrict f) finiteTypeLocallyConstant
            (restrict (𝒰.f i) F))

end CategoryTheory.Sheaf
