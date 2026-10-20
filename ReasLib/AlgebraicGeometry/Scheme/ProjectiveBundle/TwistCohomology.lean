/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.BaseChange

/-!
# Cohomology of twists on projective bundles

This file describes all higher direct images of the integral twists on a projective bundle and
records the naturality of the active identifications under base change and isomorphisms of the
defining locally free module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {S P : Scheme.{u}} {π : P ⟶ S} {ℰ : S.Modules}

/-- The integral twists in a projective-bundle presentation are the integral tensor powers of
its tautological quotient module. -/
def Representation.IsTautologicalTwistFamily
    (hπ : Representation π ℰ) : Prop :=
  ∀ d : ℤ,
    IsIsomorphic (hπ.twist d)
      (@Scheme.Modules.tensorPowerInt P (tautologicalSheaf π hπ)
        (tautologicalSheaf_isInvertible π hπ) d)

set_option maxHeartbeats 2000000 in
/-- For a positive-dimensional projective bundle of a finite locally free module of rank
`n + 1`, the higher direct images of every integral twist are the expected symmetric power in
degree zero, the internal dual of the complementary symmetric power tensored with the top
exterior power in degree `n`, and zero in every inactive case. The active identifications are
compatible with arbitrary base change and with isomorphisms of projective-bundle data. -/
theorem twistHigherDirectImage
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (hn : 1 ≤ n) (hTwist : hπ.IsTautologicalTwistFamily) :
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
                (higherIso n d).hom ≫ (topIdent' d hd).hom) := sorry

/-- In nonnegative twist degree, the degree-zero higher direct image is the corresponding
symmetric-power sheaf. -/
theorem twistHigherDirectImage_zero
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (hn : 1 ≤ n) (hTwist : hπ.IsTautologicalTwistFamily)
    (d : ℤ) (hd : 0 ≤ d) :
    IsIsomorphic
      (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) 0)
      (Sym[d.toNat] ℰ) := by
  obtain ⟨zeroIdent, _, _, _, _⟩ :=
    twistHigherDirectImage π ℰ hπ n hn hTwist
  exact ⟨zeroIdent d hd⟩

/-- Every higher direct image outside the active degree-zero and top-degree cases vanishes. -/
theorem twistHigherDirectImage_isZero_of_not_cases
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (hn : 1 ≤ n) (hTwist : hπ.IsTautologicalTwistFamily)
    (q : ℕ) (d : ℤ) (hzero : ¬ (q = 0 ∧ 0 ≤ d))
    (htop : ¬ (q = n ∧ 0 ≤ -((n : ℤ) + 1) - d)) :
    IsZero (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) q) := by
  obtain ⟨_, _, vanish, _, _⟩ :=
    twistHigherDirectImage π ℰ hπ n hn hTwist
  exact vanish q d hzero htop

/-- In the active top-degree range, the degree-`n` higher direct image is the internal dual of
the complementary symmetric power tensored with the top exterior power. -/
theorem twistHigherDirectImage_top
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (hn : 1 ≤ n) (hTwist : hπ.IsTautologicalTwistFamily)
    (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d) :
    IsIsomorphic
      (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) n)
      (((MonoidalClosed.internalHom : S.Modulesᵒᵖ ⥤ S.Modules ⥤ S.Modules).obj
        (Opposite.op
          ((Sym[(-((n : ℤ) + 1) - d).toNat] ℰ) ⊗
            (Λ[n + 1] ℰ)))).obj
          (𝟙_ S.Modules)) := by
  obtain ⟨_, topIdent, _, _, _⟩ :=
    twistHigherDirectImage π ℰ hπ n hn hTwist
  exact ⟨topIdent d hd⟩

/-- The active projective-bundle twist-cohomology identifications commute with arbitrary base
change through explicit relative-projective-spectrum comparison data. -/
theorem twistHigherDirectImage_baseChange_compatible
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (hn : 1 ≤ n) (hTwist : hπ.IsTautologicalTwistFamily)
    {S' : Scheme.{u}} (g : S' ⟶ S)
    (baseChange : Scheme.Hom.RelativeProjBaseChange hπ.presentation g) :
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
      (topHigherBaseChange : ∀ (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d),
          (Scheme.Modules.pullback g).obj
                (RingedSpace.Hom.higherDirectImageModule π.toShHom (hπ.twist d) n) ≅
            RingedSpace.Hom.higherDirectImageModule (pullback.snd π g).toShHom
              (baseChange.presentation.twist d) n)
      (topTargetBaseChange : ∀ (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d),
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
          (Scheme.Modules.pullback g).map
                ((twistHigherDirectImage π ℰ hπ n hn hTwist).choose d hd).hom ≫
              (zeroTargetBaseChange d hd).hom =
            (zeroHigherBaseChange d hd).hom ≫ (zeroIdent' d hd).hom) ∧
        ∀ (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d),
          (Scheme.Modules.pullback g).map
                ((twistHigherDirectImage π ℰ hπ n hn hTwist).choose_spec.choose d hd).hom ≫
              (topTargetBaseChange d hd).hom =
            (topHigherBaseChange d hd).hom ≫ (topIdent' d hd).hom := by
  exact
    (twistHigherDirectImage π ℰ hπ n hn hTwist).choose_spec.choose_spec.2.1 g baseChange

set_option maxHeartbeats 2000000 in
/-- The active projective-bundle twist-cohomology identifications commute with explicit
isomorphisms of the defining module, total space, and integral twists. -/
theorem twistHigherDirectImage_iso_compatible
    (π : P ⟶ S) (ℰ : S.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (hn : 1 ≤ n) (hTwist : hπ.IsTautologicalTwistFamily)
    {P' : Scheme.{u}} {ℰ' : S.Modules} (π' : P' ⟶ S)
    (hπ' : Representation π' ℰ')
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ']
    (hTwist' : hπ'.IsTautologicalTwistFamily)
    (moduleIso : ℰ ≅ ℰ') (projectiveIso : P ≅ P')
    (projectiveIso_over : projectiveIso.hom ≫ π' = π)
    (twistIso : ∀ d : ℤ,
      hπ.twist d ≅ (Scheme.Modules.pullback projectiveIso.hom).obj (hπ'.twist d)) :
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
          ((twistHigherDirectImage π ℰ hπ n hn hTwist).choose d hd).hom ≫
              (RingedSpace.SymmetricPower.mapIso moduleIso d.toNat).hom =
            (higherIso 0 d).hom ≫ (zeroIdent' d hd).hom) ∧
        ∀ (d : ℤ) (hd : 0 ≤ -((n : ℤ) + 1) - d),
          ((twistHigherDirectImage π ℰ hπ n hn hTwist).choose_spec.choose d hd).hom ≫
              (((MonoidalClosed.internalHom : S.Modulesᵒᵖ ⥤ S.Modules ⥤ S.Modules).mapIso
                (MonoidalCategory.tensorIso
                  (RingedSpace.SymmetricPower.mapIso moduleIso
                    (-((n : ℤ) + 1) - d).toNat)
                  (RingedSpace.ExteriorPower.mapIso moduleIso (n + 1))).symm.op).app
                (𝟙_ S.Modules)).hom =
            (higherIso n d).hom ≫ (topIdent' d hd).hom := by
  exact
    (twistHigherDirectImage π ℰ hπ n hn hTwist).choose_spec.choose_spec.2.2
      π' hπ' hTwist' moduleIso projectiveIso projectiveIso_over twistIso

end AlgebraicGeometry.Scheme.ProjectiveBundle
