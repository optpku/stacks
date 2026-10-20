module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RelativeForms
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 50.17.5
With notation as in More on Morphisms, Lemma 37.17.3, for every `a : ℕ` there is a unique
arrow `Rb_* Ω^a_{X'/S} ⟶ Ω^a_{X/S}` in `D(O_X)` whose composition with
`Ω^a_{X/S} ⟶ Rb_* Ω^a_{X'/S}` is the identity on `Ω^a_{X/S}`. -/
@[stacks 0G5J]
#check (AlgebraicGeometry.IsBlowup.existsUnique_relativeDifferentialRetraction :
  ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
    [Smooth f] [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] (a : ℕ),
    ∃! r :
      (RingedSpace.moduleDerivedPushforward b.toShHom).obj
          ((DerivedCategory.singleFunctor X'.Modules 0).obj
            (Λ[a] Ω[(b ≫ f).toShHom])) ⟶
        (DerivedCategory.singleFunctor X.Modules 0).obj (Λ[a] Ω[f.toShHom]),
      AlgebraicGeometry.IsBlowup.relativeDifferentialDerivedComparison f I b a ≫ r = 𝟙 _)
