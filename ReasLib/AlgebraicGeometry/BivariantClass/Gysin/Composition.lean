/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Composition

/-!
# Composition of local complete intersection Gysin classes

Gysin existence descends from a composite to its first factor. The geometric
Gysin coefficients compose on common normal-rank and smooth-dimension strata.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle Gysin

/-- If a composite admits an immersion–smooth factorization, its first factor does too. -/
theorem hasGysinMap_of_comp
    {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HasGysinMap (f ≫ g) → HasGysinMap f := sorry

/-- For composable local complete intersection morphisms over a universally catenary
dimension-function base, existence of Gysin maps for the second morphism and the composite
implies existence for the first. There are regular-immersion–smooth factorizations with
normal-bundle deformation realizations whose integer-degree Gysin coefficients compose on
every common rank/dimension stratum and vanish outside the sum of the local virtual degrees. -/
theorem gysin_comp_lci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection g.left]
    (hfg : HasGysinMap (f ≫ g)) (hg : HasGysinMap g) :
    HasGysinMap f ∧
    ∃ (P : Over S) (finiteTypeP : LocallyOfFiniteType P.hom)
      (i : X ⟶ P) (σ : P ⟶ Y) (regularI : IsRegularImmersion i.left)
      (smoothSigma : Smooth σ.left) (hfac : i ≫ σ = f),
    ∃ (ef : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
      (Df : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
        i.left.liftCoborder
        (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
        (normalBundle i.left ef).toCoborder),
    ∃ (Q : Over S) (finiteTypeQ : LocallyOfFiniteType Q.hom)
      (j : Y ⟶ Q) (τ : Q ⟶ Z) (regularJ : IsRegularImmersion j.left)
      (smoothTau : Smooth τ.left) (hfacg : j ≫ τ = g),
    ∃ (eg : Scheme.Modules.dual (normalSheaf j.left) ≅ conormalSheaf j.left)
      (Dg : ClosedDeformation Y.hom (j.left.coborderRange.ι ≫ Q.hom)
        j.left.liftCoborder
        (by rw [← Category.assoc, j.left.liftCoborder_ι]; exact Over.w j)
        (normalBundle j.left eg).toCoborder),
    ∃ (R : Over S) (finiteTypeR : LocallyOfFiniteType R.hom)
      (k : X ⟶ R) (ρ : R ⟶ Z) (regularK : IsRegularImmersion k.left)
      (smoothRho : Smooth ρ.left) (hfacfg : k ≫ ρ = f ≫ g),
    ∃ (efg : Scheme.Modules.dual (normalSheaf k.left) ≅ conormalSheaf k.left)
      (Dfg : ClosedDeformation X.hom (k.left.coborderRange.ι ≫ R.hom)
        k.left.liftCoborder
        (by rw [← Category.assoc, k.left.liftCoborder_ι]; exact Over.w k)
        (normalBundle k.left efg).toCoborder),
    ∀ (rt su : ℕ × ℕ) (p : ℤ),
      let V := factorizationRankLoci j τ eg su
      let U := factorizationRankLoci i σ ef rt ⊓ f.left ⁻¹ᵁ V
      let a : ℤ := (rt.1 : ℤ) - rt.2
      let b : ℤ := (su.1 : ℤ) - su.2
      ComponentRestriction.restrict δ (f ≫ g) p U ⊤ (by simp)
          (factorizationClassDegree δ (f ≫ g) k ρ hfacfg efg Dfg p) =
        if degree : a + b = p then
          (by
            have c := comp δ
              (ComponentRestriction.hom f U V inf_le_right)
              (ComponentRestriction.hom g V ⊤ (by simp))
              (ComponentRestriction.restrict δ f a U V inf_le_right
                (factorizationClassDegree δ f i σ hfac ef Df a))
              (ComponentRestriction.restrict δ g b V ⊤ (by simp)
                (factorizationClassDegree δ g j τ hfacg eg Dg b))
            rw [ComponentRestriction.hom_comp f g U V ⊤ inf_le_right
              (by simp) (by simp)] at c
            exact degree ▸ c)
        else pointwiseZero δ (ComponentRestriction.hom (f ≫ g) U ⊤ (by simp)) p := sorry

end AlgebraicGeometry.BivariantClass
