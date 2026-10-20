module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineFppfDerived

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 59.101.3 (1): every term of the tensor presheaf complex on the affine fppf site
is a sheaf. -/
@[stacks 0H0U] #check (AlgebraicGeometry.Scheme.AffineFppf.tensorPresheafComplex_isSheaf :
  ∀ (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ),
    Presheaf.IsSheaf (bigAffineFppfTopology (Spec A))
      ((AlgebraicGeometry.Scheme.AffineFppf.tensorPresheafComplex A M).X degree))

/- Lemma 59.101.3 (2): the canonical map from an arbitrary module complex to its derived
affine-fppf global sections is a quasi-isomorphism. -/
@[stacks 0H0U] #check (AlgebraicGeometry.Scheme.AffineFppf.isIso_toDerivedGamma :
  ∀ (A : CommRingCat.{u})
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasDerivedCategory (AlgebraicGeometry.Scheme.AffineFppf.AbelianSheaf A)]
    [HasDerivedCategory AddCommGrpCat.{u}] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (RF : DerivedCategory (AlgebraicGeometry.Scheme.AffineFppf.AbelianSheaf A) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (α : CategoryTheory.Functor.RightDerived.Cochain.toDerived
      (AlgebraicGeometry.Scheme.AffineFppf.globalSections A) ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (AlgebraicGeometry.Scheme.AffineFppf.AbelianSheaf A)
        (ComplexShape.up ℤ))],
    IsIso (AlgebraicGeometry.Scheme.AffineFppf.toDerivedGamma A M RF α))
