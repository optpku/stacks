module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Nonvanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.67.1: the source-facing statement is supplied by the reusable
inverse-limit étale cohomology nonvanishing theorem. -/
@[stacks 0DV7] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_ellPowerTorsion_nonvanishing_iff :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {ℓ n : ℕ} [Fact (Nat.Prime ℓ)] (hn : 0 < n)
      (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (D : OrderDual I ⥤ Scheme.{u})
      (g : ∀ i : I, D.obj (OrderDual.toDual i) ⟶ S)
      (hg : ∀ (i j : I) (hij : i ≤ j),
        OrderDualInverseSystem.transitionMap D hij ≫ g i = g j)
      [∀ i : I, IsFinite (g i)] [∀ i : I, Etale (g i)]
      (hd : ∀ i : I, FiniteEtale.IsConstantDegreePrimeTo (g i) ℓ)
      (c : Cone D) (gX : c.pt ⟶ S)
      (hgX : ∀ i : I, c.π.app (OrderDual.toDual i) ≫ g i = gX)
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
      [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology c.pt.smallEtaleTopology).IsRightAdjoint]
      (hc : IsLimit c),
      (∃ G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u},
          CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ G ∧
            ¬ IsZero (G.H' n (globalEtale S))) ↔
        ∃ F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u},
          CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F ∧
            ¬ IsZero (F.H' n (globalEtale c.pt)))

/- The inverse-image coefficient transport is supplied by
the reusable theorem with all inverse-system hypotheses retained. -/
#check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_ellPowerTorsion_of_pullback :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {ℓ n : ℕ} [Fact (Nat.Prime ℓ)] (hn : 0 < n)
      (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (D : OrderDual I ⥤ Scheme.{u})
      (g : ∀ i : I, D.obj (OrderDual.toDual i) ⟶ S)
      (hg : ∀ (i j : I) (hij : i ≤ j),
        OrderDualInverseSystem.transitionMap D hij ≫ g i = g j)
      [∀ i : I, IsFinite (g i)] [∀ i : I, Etale (g i)]
      (hd : ∀ i : I, FiniteEtale.IsConstantDegreePrimeTo (g i) ℓ)
      (c : Cone D) (gX : c.pt ⟶ S)
      (hgX : ∀ i : I, c.π.app (OrderDual.toDual i) ≫ g i = gX)
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
      [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology c.pt.smallEtaleTopology).IsRightAdjoint]
      (hc : IsLimit c)
      (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (hG : CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ G)
      (hG' : ¬ IsZero (G.H' n (globalEtale S))),
      CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ
          (((smallEtalePullback gX).sheafPullback AddCommGrpCat.{u}
            S.smallEtaleTopology c.pt.smallEtaleTopology).obj G) ∧
        ¬ IsZero
            ((((smallEtalePullback gX).sheafPullback AddCommGrpCat.{u}
                S.smallEtaleTopology c.pt.smallEtaleTopology).obj G).H' n
              (globalEtale c.pt)))

/- The direct-image coefficient transport is supplied by
the reusable theorem with all inverse-system hypotheses retained. -/
#check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_ellPowerTorsion_of_pushforward :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {ℓ n : ℕ} [Fact (Nat.Prime ℓ)] (hn : 0 < n)
      (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (D : OrderDual I ⥤ Scheme.{u})
      (g : ∀ i : I, D.obj (OrderDual.toDual i) ⟶ S)
      (hg : ∀ (i j : I) (hij : i ≤ j),
        OrderDualInverseSystem.transitionMap D hij ≫ g i = g j)
      [∀ i : I, IsFinite (g i)] [∀ i : I, Etale (g i)]
      (hd : ∀ i : I, FiniteEtale.IsConstantDegreePrimeTo (g i) ℓ)
      (c : Cone D) (gX : c.pt ⟶ S)
      (hgX : ∀ i : I, c.π.app (OrderDual.toDual i) ≫ g i = gX)
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
      [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology c.pt.smallEtaleTopology).IsRightAdjoint]
      (hc : IsLimit c)
      (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})
      (hF : CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F)
      (hF' : ¬ IsZero (F.H' n (globalEtale c.pt))),
      CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ
          (((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
            S.smallEtaleTopology c.pt.smallEtaleTopology).obj F) ∧
        ¬ IsZero
            ((((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
                S.smallEtaleTopology c.pt.smallEtaleTopology).obj F).H' n
              (globalEtale S)))

end AlgebraicGeometry.Scheme.Etale

end
