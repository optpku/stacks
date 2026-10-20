module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.Commutation

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

universe u

/- Lemma 42.54.8: in Situation 42.7.1, if `X` is locally of finite type over `S`,
`i : Z ⟶ X` is a closed immersion with virtual normal sheaf `𝒩`, and `Y ⟶ X` is
locally of finite type, then every homogeneous class `c ∈ A^*(Y ⟶ X)` commutes with
the virtual-normal class `c(Z ⟶ X, 𝒩)` in the sense of Remark 42.33.6. -/
@[stacks 0FBP] #check
  (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_commute :
    ∀ {S X Z Y : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [LocallyOfFiniteType pZ]
    (i : Z ⟶ X) (hi : i ≫ pX = pZ) [IsClosedImmersion i]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) [LocallyOfFiniteType f]
    (V : VirtualNormalBundle i) (D : ClosedDeformation pZ pX i hi V)
    (q : ℤ) (c : BivariantClass δ (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX) q)
    (r : ℕ),
    BivariantClass.Commute δ
      (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX) (overHom pZ pX i hi)
      c (globalClassOfRank δ pZ pX i hi V D r))
