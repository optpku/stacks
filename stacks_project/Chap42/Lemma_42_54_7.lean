module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ZeroScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.54.7: for a scheme locally of finite type over a situation `(S, δ)`, the
degree-one Gysin bivariant class of a zero-scheme triple `(ℒ, s, i : D ⟶ X)` equals the
degree-one virtual-normal class `c(D ⟶ X, 𝒩)` formed from `𝒩 = i*ℒ`. -/
@[stacks 0FBN] #check
  (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.gysin_eq_ofZeroScheme :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
      (D : Scheme.Hom.VirtualNormalBundle.ClosedDeformation
        (Scheme.zeroSchemeι ℒ s ≫ X.hom) X.hom (Scheme.zeroSchemeι ℒ s) rfl
        (Scheme.Hom.VirtualNormalBundle.ofZeroScheme ℒ s)),
      BivariantClass.gysin δ X ℒ s =
        Scheme.Hom.VirtualNormalBundle.globalClassOfRank δ
          (Scheme.zeroSchemeι ℒ s ≫ X.hom) X.hom (Scheme.zeroSchemeι ℒ s) rfl
          (Scheme.Hom.VirtualNormalBundle.ofZeroScheme ℒ s) D 1)

