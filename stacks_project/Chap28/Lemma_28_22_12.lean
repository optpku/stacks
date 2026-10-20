module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/- Lemma 28.22.12: a finite quasi-coherent algebra on a quasi-compact quasi-separated scheme is
a filtered colimit of finite, quasi-coherent, finitely presentable algebra sheaves with
locally surjective transition maps. -/
@[stacks 086N] #check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.exists_finite_finitelyPresentable_colimitPresentation_locallySurjective :
    ∀ {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (A : S.QcAlgebraUnder),
      AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteProperty S A.obj →
        ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
          ∃ pres : ColimitPresentation I A.obj,
            (∀ i : I, AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteProperty S
              (pres.diag.obj i)) ∧
              (∀ i : I,
                AlgebraicGeometry.Scheme.QcAlgebraUnder.finitelyPresentableProperty S
                  (pres.diag.obj i)) ∧
                ∀ {i i' : I} (f : i ⟶ i'),
                  CategoryTheory.Sheaf.IsLocallySurjective (pres.diag.map f).right)

end
