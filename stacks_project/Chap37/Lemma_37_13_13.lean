module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.FormallySmoothPresentation

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 37.13.13: if `f : X ⟶ Y` factors as an immersion `i : X ⟶ P` followed by
a formally smooth morphism `g : P ⟶ Y`, then `NL(f)` is isomorphic in `D(𝒪_X)` to the
two-term complex `C_{X/P} ⟶ i^* Ω_{P/Y}`, with the conormal sheaf in degree `-1`. -/
@[stacks 0FV4] #check
  (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.isomorphicConormalDifferentials :
    ∀ {X P Y : Scheme.{u}} (f : X ⟶ Y) (i : X ⟶ P) (g : P ⟶ Y)
      (hfactor : i ≫ g = f) [IsImmersion i] [FormallySmooth g],
    IsIsomorphic
      ((DerivedCategory.Q : CochainComplex X.toRingedSpace.Modules ℤ ⥤
        RingedSpace.ModuleDerived X.toRingedSpace).obj
          (RingedSpace.naiveCotangent f.toShHom))
      ((DerivedCategory.Q : CochainComplex X.toRingedSpace.Modules ℤ ⥤
        RingedSpace.ModuleDerived X.toRingedSpace).obj
          (HomologicalComplex.double
            (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.map i g)
            (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1)))))
