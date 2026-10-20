/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.MayerVietoris
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.50.1 (Mayer-Vietoris for étale cohomology) (1) -/
@[stacks 0A50] #check
  (EtaleMayerVietoris.mayerVietorisEtaleExact :
    ∀ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤),
      [hweak : HasWeakSheafify X.smallEtaleTopology (Type u)] →
      [hsheaf : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] →
      [hext : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] →
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u},
        (((EtaleMayerVietoris.square X U V hUV).sequence F 0 1 rfl).zeroPrecomp 1).Exact ∧
          ∀ n : ℕ,
            ((EtaleMayerVietoris.square X U V hUV).sequence F n (n + 1) rfl).Exact)

/- Lemma 59.50.1 (Mayer-Vietoris for étale cohomology) (2) -/
@[stacks 0A50] #check
  (EtaleMayerVietoris.mayerVietorisEtaleFunctorial :
    ∀ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤),
      [hweak : HasWeakSheafify X.smallEtaleTopology (Type u)] →
      [hsheaf : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] →
      [hext : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] →
      (n : ℕ) →
      {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} → (φ : F ⟶ G) →
      (EtaleMayerVietoris.sequenceFunctor
          (EtaleMayerVietoris.square X U V hUV) n).obj F =
          (EtaleMayerVietoris.square X U V hUV).sequence F n (n + 1) rfl ∧
        (EtaleMayerVietoris.sequenceFunctor
          (EtaleMayerVietoris.square X U V hUV) n).map φ =
          EtaleMayerVietoris.sequenceMap
            (EtaleMayerVietoris.square X U V hUV) φ n)
