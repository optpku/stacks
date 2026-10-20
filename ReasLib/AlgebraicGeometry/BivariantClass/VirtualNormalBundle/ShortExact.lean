module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ChowGroup.VectorBundle.ShortExact

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace VirtualNormalBundle
namespace ShortExact

/-- The restriction of the closed immersion to the joint rank locus of the subbundle
and quotient. -/
noncomputable def rankPairHom
    {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    @rankPairOver
        S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
        V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE ⟶
      BivariantClass.ComponentRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.ComponentRestriction.hom
    (overHom (i ≫ p) p i rfl)
    (@rankPairClopen
      Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
      (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
    (by simp)

/-- `rankPairHom` is the canonical open restriction of the original closed immersion. -/
theorem rankPairHom_def
    {S Z X : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree] (r' rE : ℕ) :
    rankPairHom p i V' V E ι πE hzero r' rE =
      BivariantClass.ComponentRestriction.hom
        (overHom (i ≫ p) p i rfl)
        (@rankPairClopen
          Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
          (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
        (by simp) := rfl

/-- The homogeneous virtual-normal class restricted to a common joint rank locus. -/
noncomputable def restrictedGlobalClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] (V' V W : VirtualNormalBundle i)
    (E : Z.Modules) (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E)
    (hzero : ι ≫ πE = 0) [E.IsFiniteLocallyFree]
    (D : ClosedDeformation (i ≫ p) p i rfl W) (r' rE n : ℕ) :
    BivariantClass delta (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ) :=
  BivariantClass.ComponentRestriction.restrict delta
    (overHom (i ≫ p) p i rfl) (n : ℤ)
    (@rankPairClopen
      Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
      (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
    (by simp)
    (globalClassOfRank delta (i ≫ p) p i rfl W D n)

/-- `restrictedGlobalClass` is open restriction of the global homogeneous
virtual-normal class. -/
theorem restrictedGlobalClass_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] (V' V W : VirtualNormalBundle i)
    (E : Z.Modules) (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E)
    (hzero : ι ≫ πE = 0) [E.IsFiniteLocallyFree]
    (D : ClosedDeformation (i ≫ p) p i rfl W) (r' rE n : ℕ) :
    restrictedGlobalClass delta p i V' V W E ι πE hzero D r' rE n =
      BivariantClass.ComponentRestriction.restrict delta
        (overHom (i ≫ p) p i rfl) (n : ℤ)
        (@rankPairClopen
          Z (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
          (inferInstance : E.IsFiniteLocallyFree) r' rE).toOpens ⊤
        (by simp)
        (globalClassOfRank delta (i ≫ p) p i rfl W D n) := rfl

/-- For a short exact sequence `0 ⟶ V'.module ⟶ V.module ⟶ E ⟶ 0`
whose dual inclusion factors the virtual-normal quotient map, the virtual-normal class
of `V` is the composition of the top Chern class of `E` with that of `V'`, on every
joint rank locus. -/
theorem closedClass_eq_topChern_comp
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree]
    (hshort : (CategoryTheory.ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : V.map = Scheme.Modules.dualMap ι ≫ V'.map)
    (D' : ClosedDeformation (i ≫ p) p i rfl V')
    (D : ClosedDeformation (i ≫ p) p i rfl V) (r' rE : ℕ) :
    @DirectSum.of ℕ
        (fun n : ℕ ↦ BivariantClass delta
          (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ))
        (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
          (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ)).toAddCommMonoid)
        inferInstance
        (r' + rE)
        (restrictedGlobalClass delta p i V' V V E ι πE hzero D r' rE (r' + rE)) =
      BivariantClass.Nonnegative.castHom delta
        (CategoryTheory.Category.id_comp (rankPairHom p i V' V E ι πE hzero r' rE))
        (BivariantClass.Nonnegative.comp delta
          (𝟙 (@rankPairOver
            S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
            V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE))
          (rankPairHom p i V' V E ι πE hzero r' rE)
          (@DirectSum.of ℕ
            (fun n : ℕ ↦ BivariantClass delta
              (𝟙 (@rankPairOver
                S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
                V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE))
              (n : ℤ))
            (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
              (𝟙 (@rankPairOver
                S (Over.mk (i ≫ p)) (CategoryTheory.ShortComplex.mk ι πE hzero)
                V'.isFiniteLocallyFree (inferInstance : E.IsFiniteLocallyFree) r' rE)) (n : ℤ)).toAddCommMonoid)
            inferInstance rE
            (@rankPairTopChern
              S _ delta _ (Over.mk (i ≫ p)) _ (ChernClass.Theory.canonical delta (i ≫ p))
              (CategoryTheory.ShortComplex.mk ι πE hzero) V'.isFiniteLocallyFree
              (inferInstance : E.IsFiniteLocallyFree) r' rE))
          (@DirectSum.of ℕ
            (fun n : ℕ ↦ BivariantClass delta
              (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ))
            (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
              (rankPairHom p i V' V E ι πE hzero r' rE) (n : ℤ)).toAddCommMonoid)
            inferInstance r'
            (restrictedGlobalClass delta p i V' V V' E ι πE hzero D' r' rE r'))) := sorry

end ShortExact
end VirtualNormalBundle
end Hom
end Scheme
end AlgebraicGeometry
