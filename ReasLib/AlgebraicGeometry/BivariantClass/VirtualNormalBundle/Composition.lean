module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity
public import ReasLib.AlgebraicGeometry.BivariantClass.FiniteSum

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

open Hom.Conormal.Transitivity

/-- The degree-`n` homogeneous convolution of the virtual-normal classes of two
nested closed immersions, viewed on their composite. -/
noncomputable def globalClassConvolution
    {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V' : VirtualNormalBundle i)
    (D' : ClosedDeformation (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedDeformation (j ≫ p) p j rfl V'') (n : ℕ) :
    BivariantClass delta (overHom (i ≫ j ≫ p) p (i ≫ j) rfl) (n : ℤ) :=
  (show overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl =
      overHom (i ≫ j ≫ p) p (i ≫ j) rfl from by
    unfold overHom
    exact (Over.homMk_comp (U := Over.mk (i ≫ j ≫ p))
      (V := Over.mk (j ≫ p)) (W := Over.mk p) i j rfl rfl).symm) ▸
    BivariantClass.pointwiseSum delta
      (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl)
      (n : ℤ) Finset.univ
      (fun ij : Finset.antidiagonal n ↦
        BivariantClass.Nonnegative.castGrading delta
          (BivariantClass.Nonnegative.antidiagonalDegree n ij)
          (BivariantClass.comp delta
            (overHom (i ≫ j ≫ p) (j ≫ p) i rfl) (overHom (j ≫ p) p j rfl)
            (globalClassOfRank delta (i ≫ j ≫ p) (j ≫ p) i rfl V' D' ij.1.1)
            (globalClassOfRank delta (j ≫ p) p j rfl V'' D'' ij.1.2)))

/-- The homogeneous convolution is the transported finite sum of compositions over all
pairs of nonnegative degrees with total degree `n`. -/
theorem globalClassConvolution_apply
    {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V' : VirtualNormalBundle i)
    (D' : ClosedDeformation (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedDeformation (j ≫ p) p j rfl V'') (n : ℕ) :
    globalClassConvolution delta p j i V' D' V'' D'' n =
      (show overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl =
          overHom (i ≫ j ≫ p) p (i ≫ j) rfl from by
        unfold overHom
        exact (Over.homMk_comp (U := Over.mk (i ≫ j ≫ p))
          (V := Over.mk (j ≫ p)) (W := Over.mk p) i j rfl rfl).symm) ▸
        BivariantClass.pointwiseSum delta
          (overHom (i ≫ j ≫ p) (j ≫ p) i rfl ≫ overHom (j ≫ p) p j rfl)
          (n : ℤ) Finset.univ
          (fun ij : Finset.antidiagonal n ↦
            BivariantClass.Nonnegative.castGrading delta
              (BivariantClass.Nonnegative.antidiagonalDegree n ij)
              (BivariantClass.comp delta
                (overHom (i ≫ j ≫ p) (j ≫ p) i rfl) (overHom (j ≫ p) p j rfl)
                (globalClassOfRank delta (i ≫ j ≫ p) (j ≫ p) i rfl V' D' ij.1.1)
                (globalClassOfRank delta (j ≫ p) p j rfl V'' D'' ij.1.2))) := rfl

/-- For nested closed immersions, compatible virtual normal bundles whose duals form a
short exact sequence over the conormal transitivity sequence have completed Gysin classes
satisfying the composition identity in every nonnegative degree. -/
theorem closedClass_comp
    {S Z Y X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ p)]
    (i : Z ⟶ Y) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ j ≫ p)]
    (V : VirtualNormalBundle (i ≫ j))
    (D : ClosedDeformation (i ≫ j ≫ p) p (i ≫ j) rfl V)
    (V' : VirtualNormalBundle i)
    (D' : ClosedDeformation (i ≫ j ≫ p) (j ≫ p) i rfl V')
    (V'' : VirtualNormalBundle j)
    (D'' : ClosedDeformation (j ≫ p) p j rfl V'')
    (incl :
      (Scheme.Modules.pullback i).obj (Scheme.Modules.dual V''.module) ⟶
        Scheme.Modules.dual V.module)
    (proj : Scheme.Modules.dual V.module ⟶ Scheme.Modules.dual V'.module)
    (hzero : incl ≫ proj = 0) (hshort : (ShortComplex.mk incl proj hzero).ShortExact)
    (h_left :
      CommSq incl ((Scheme.Modules.pullback i).map V''.map) V.map
        (baseChange i j))
    (h_right :
      CommSq proj V.map V'.map (projection i j))
    (n : ℕ) :
    globalClassOfRank delta (i ≫ j ≫ p) p (i ≫ j) rfl V D n =
      globalClassConvolution delta p j i V' D' V'' D'' n := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
