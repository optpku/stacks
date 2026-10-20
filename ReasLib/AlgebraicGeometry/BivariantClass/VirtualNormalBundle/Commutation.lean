module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- Every integer-degree bivariant class into a scheme commutes with every global
homogeneous component of the completed virtual-normal class of a closed immersion
into that scheme. -/
theorem closedClass_commute
    {S X Z Y : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [LocallyOfFiniteType pZ]
    (i : Z ⟶ X) (hi : i ≫ pX = pZ) [IsClosedImmersion i]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) [LocallyOfFiniteType f]
    (V : VirtualNormalBundle i) (D : ClosedDeformation pZ pX i hi V)
    (q : ℤ) (c : BivariantClass δ (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX) q)
    (r : ℕ) :
    BivariantClass.Commute δ
      (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX) (overHom pZ pX i hi)
      c (globalClassOfRank δ pZ pX i hi V D r) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
