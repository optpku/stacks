module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ShortExact

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact
open scoped DirectSum

universe u

namespace AlgebraicGeometry

/- Lemma 42.54.3: a short exact sequence of virtual normal sheaves with factored
conormal quotient expresses the ambient class as the quotient top Chern class
composed with the subbundle class on every joint rank locus. -/
@[stacks 0FBL] #check
  (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.ShortExact.closedClass_eq_topChern_comp :
    ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V' V : VirtualNormalBundle i) (E : Z.Modules)
    (ι : V'.module ⟶ V.module) (πE : V.module ⟶ E) (hzero : ι ≫ πE = 0)
    [E.IsFiniteLocallyFree]
    (hshort : (CategoryTheory.ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : V.map = Scheme.Modules.dualMap ι ≫ V'.map)
    (D' : ClosedDeformation (i ≫ p) p i rfl V')
    (D : ClosedDeformation (i ≫ p) p i rfl V) (r' rE : ℕ),
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
            (restrictedGlobalClass delta p i V' V V' E ι πE hzero D' r' rE r'))))

end AlgebraicGeometry
