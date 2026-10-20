/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.EllPowerTorsion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteEtaleDegree
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [hI : Nonempty I] [hDirected : IsDirected I (· ≤ ·)]
variable {ℓ n : ℕ} [instℓ : Fact (Nat.Prime ℓ)]
variable (hn : 0 < n)
variable (S : Scheme.{u}) [hCompact : CompactSpace S] [hQuasiSeparated : QuasiSeparatedSpace S]
variable (D : OrderDual I ⥤ Scheme.{u})
variable (g : ∀ i : I, D.obj (OrderDual.toDual i) ⟶ S)
variable (hg : ∀ (i j : I) (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap D hij ≫ g i = g j)
variable [hFinite : ∀ i : I, IsFinite (g i)] [hEtale : ∀ i : I, Etale (g i)]
variable (hd : ∀ i : I, FiniteEtale.IsConstantDegreePrimeTo (g i) ℓ)
variable (c : Cone D)
variable (gX : c.pt ⟶ S)
variable (hgX : ∀ i : I, c.π.app (OrderDual.toDual i) ≫ g i = gX)
variable [hSheafifyS : HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [hExtS : HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [hSheafifyX : HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [hExtX : HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [hAdjX :
    ((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology c.pt.smallEtaleTopology).IsRightAdjoint]

include hI hDirected instℓ hn hCompact hQuasiSeparated hg hFinite hEtale hd hgX
  hSheafifyS hExtS hSheafifyX hExtX hAdjX

/-- For a directed inverse limit of finite étale covers of degree prime to `ℓ`,
nonvanishing degree-`n` étale cohomology with locally `ℓ`-power torsion
coefficients is equivalent on the base and on the limit. -/
theorem etaleCohomology_ellPowerTorsion_nonvanishing_iff (hc : IsLimit c) :
    (∃ G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u},
        CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ G ∧
          ¬ IsZero (G.H' n (globalEtale S))) ↔
      ∃ F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u},
        CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F ∧
          ¬ IsZero (F.H' n (globalEtale c.pt)) := sorry

/-- Pulling back a locally `ℓ`-power torsion coefficient sheaf preserves
nonvanishing degree-`n` étale cohomology in the inverse-limit situation. -/
theorem etaleCohomology_ellPowerTorsion_of_pullback (hc : IsLimit c)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (hG : CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ G)
    (hG' : ¬ IsZero (G.H' n (globalEtale S))) :
    CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ
        (((smallEtalePullback gX).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology c.pt.smallEtaleTopology).obj G) ∧
      ¬ IsZero
          ((((smallEtalePullback gX).sheafPullback AddCommGrpCat.{u}
              S.smallEtaleTopology c.pt.smallEtaleTopology).obj G).H' n
            (globalEtale c.pt)) := sorry

/-- Pushing forward a locally `ℓ`-power torsion coefficient sheaf preserves
nonvanishing degree-`n` étale cohomology in the inverse-limit situation. -/
theorem etaleCohomology_ellPowerTorsion_of_pushforward (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})
    (hF : CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F)
    (hF' : ¬ IsZero (F.H' n (globalEtale c.pt))) :
    CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ
        (((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology c.pt.smallEtaleTopology).obj F) ∧
      ¬ IsZero
          ((((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
              S.smallEtaleTopology c.pt.smallEtaleTopology).obj F).H' n
            (globalEtale S)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
