module

import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.TwistCohomology
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

/- Lemma 30.8.4

For a positive-dimensional projective bundle associated to a finite locally free module of
rank `n + 1`, the higher direct images of every integral twist are the corresponding symmetric
power in degree zero, zero outside the active degrees, and the internal dual of the complementary
symmetric power tensored with the top exterior power in degree `n`. These identifications commute
with base change and with isomorphisms of projective-bundle data.
-/
@[stacks 01XX] #check (
  AlgebraicGeometry.Scheme.ProjectiveBundle.twistHigherDirectImage :
    ∀ {S P : Scheme.{u}} (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ),
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ] →
    1 ≤ n → hπ.IsTautologicalTwistFamily →
    ∃ (zeroIdent : ∀ (d : ℤ), 0 ≤ d →
          (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) 0 ≅
            Sym[d.toNat] ℰ))
      (topIdent : ∀ (d : ℤ), 0 ≤ -((n : ℤ) + 1) - d →
          (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) n ≅
            ((MonoidalClosed.internalHom : S.Modulesᵒᵖ ⥤ S.Modules ⥤ S.Modules).obj
              (Opposite.op
                ((Sym[(-((n : ℤ) + 1) - d).toNat] ℰ) ⊗
                  (Λ[n + 1] ℰ)))).obj
                (𝟙_ S.Modules))),
      (∀ (q : ℕ) (d : ℤ), ¬ (q = 0 ∧ 0 ≤ d) →
          ¬ (q = n ∧ 0 ≤ -((n : ℤ) + 1) - d) →
          IsZero (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) q)) ∧
      (∀ {S' : Scheme.{u}} (g : S' ⟶ S)
          (baseChange : Scheme.Hom.RelativeProjBaseChange hπ.presentation g),
        ∃ (zeroIdent' : ∀ (d : ℤ), 0 ≤ d →
              (RingedSpace.Hom.higherDirectImageModule (pullback.snd π g).toShHom
                  (baseChange.presentation.twist d) 0 ≅
                Sym[d.toNat] ((Scheme.Modules.pullback g).obj ℰ)))
          (topIdent' : ∀ (d : ℤ), 0 ≤ -((n : ℤ) + 1) - d →
              (RingedSpace.Hom.higherDirectImageModule (pullback.snd π g).toShHom
                  (baseChange.presentation.twist d) n ≅
                ((MonoidalClosed.internalHom : S'.Modulesᵒᵖ ⥤ S'.Modules ⥤ S'.Modules).obj
                  (Opposite.op
                    ((Sym[(-((n : ℤ) + 1) - d).toNat]
                        ((Scheme.Modules.pullback g).obj ℰ)) ⊗
                      (Λ[n + 1] ((Scheme.Modules.pullback g).obj ℰ))))).obj
                    (𝟙_ S'.Modules)))
          (zeroHigherBaseChange : ∀ (d : ℤ) (hd : 0 ≤ d),
              (Scheme.Modules.pullback g).obj
                    (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) 0) ≅
                RingedSpace.Hom.higherDirectImageModule (pullback.snd π g).toShHom
                  (baseChange.presentation.twist d) 0)
          (zeroTargetBaseChange : ∀ (d : ℤ) (hd : 0 ≤ d),
              (Scheme.Modules.pullback g).obj (Sym[d.toNat] ℰ) ≅
                Sym[d.toNat] ((Scheme.Modules.pullback g).obj ℰ))
          (topHigherBaseChange : ∀ (d : ℤ)
              (hd : 0 ≤ -((n : ℤ) + 1) - d),
              (Scheme.Modules.pullback g).obj
                    (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) n) ≅
                RingedSpace.Hom.higherDirectImageModule (pullback.snd π g).toShHom
                  (baseChange.presentation.twist d) n)
          (topTargetBaseChange : ∀ (d : ℤ)
              (hd : 0 ≤ -((n : ℤ) + 1) - d),
              (Scheme.Modules.pullback g).obj
                    (((MonoidalClosed.internalHom : S.Modulesᵒᵖ ⥤ S.Modules ⥤ S.Modules).obj
                      (Opposite.op
                        ((Sym[(-((n : ℤ) + 1) - d).toNat] ℰ) ⊗
                          (Λ[n + 1] ℰ)))).obj
                        (𝟙_ S.Modules)) ≅
                ((MonoidalClosed.internalHom : S'.Modulesᵒᵖ ⥤ S'.Modules ⥤ S'.Modules).obj
                  (Opposite.op
                    ((Sym[(-((n : ℤ) + 1) - d).toNat]
                        ((Scheme.Modules.pullback g).obj ℰ)) ⊗
                      (Λ[n + 1] ((Scheme.Modules.pullback g).obj ℰ))))).obj
                    (𝟙_ S'.Modules)),
          (∀ (d : ℤ) (hd : 0 ≤ d),
              (Scheme.Modules.pullback g).map (zeroIdent d hd).hom ≫
                  (zeroTargetBaseChange d hd).hom =
                (zeroHigherBaseChange d hd).hom ≫ (zeroIdent' d hd).hom) ∧
            ∀ (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d),
              (Scheme.Modules.pullback g).map (topIdent d hd).hom ≫
                  (topTargetBaseChange d hd).hom =
                (topHigherBaseChange d hd).hom ≫ (topIdent' d hd).hom) ∧
      (∀ {P' : Scheme.{u}} {ℰ' : S.Modules} (π' : P' ⟶ S)
          (hπ' : Representation π' ℰ')
          [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ']
          (hTwist' : hπ'.IsTautologicalTwistFamily)
          (moduleIso : ℰ ≅ ℰ') (projectiveIso : P ≅ P')
          (projectiveIso_over : projectiveIso.hom ≫ π' = π)
          (twistIso : ∀ d : ℤ,
            hπ.twist d ≅ (Scheme.Modules.pullback projectiveIso.hom).obj (hπ'.twist d)),
        ∃ (zeroIdent' : ∀ (d : ℤ), 0 ≤ d →
              (RingedSpace.Hom.higherDirectImageModule π'.toShHom (hπ'.twist d) 0 ≅
                Sym[d.toNat] ℰ'))
          (topIdent' : ∀ (d : ℤ), 0 ≤ -((n : ℤ) + 1) - d →
              (RingedSpace.Hom.higherDirectImageModule π'.toShHom (hπ'.twist d) n ≅
                ((MonoidalClosed.internalHom : S.Modulesᵒᵖ ⥤ S.Modules ⥤ S.Modules).obj
                  (Opposite.op
                    ((Sym[(-((n : ℤ) + 1) - d).toNat] ℰ') ⊗
                      (Λ[n + 1] ℰ')))).obj
                    (𝟙_ S.Modules)))
          (higherIso : ∀ (q : ℕ) (d : ℤ),
              RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) q ≅
                RingedSpace.Hom.higherDirectImageModule π'.toShHom (hπ'.twist d) q),
          (∀ (d : ℤ) (hd : 0 ≤ d),
              (zeroIdent d hd).hom ≫
                  (RingedSpace.SymmetricPower.mapIso moduleIso d.toNat).hom =
                (higherIso 0 d).hom ≫ (zeroIdent' d hd).hom) ∧
            ∀ (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d),
              (topIdent d hd).hom ≫
                  (((MonoidalClosed.internalHom : S.Modulesᵒᵖ ⥤ S.Modules ⥤ S.Modules).mapIso
                    (MonoidalCategory.tensorIso
                      (RingedSpace.SymmetricPower.mapIso moduleIso
                        (-((n : ℤ) + 1) - d).toNat)
                      (RingedSpace.ExteriorPower.mapIso moduleIso (n + 1))).symm.op).app
                    (𝟙_ S.Modules)).hom =
                (higherIso n d).hom ≫ (topIdent' d hd).hom)
)

end AlgebraicGeometry.Scheme.ProjectiveBundle
