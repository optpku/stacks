/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TensorSplitting.Unit

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 42.32.7 (1): the zero scheme of a section of an invertible module
admits a unit-factor tensor-section splitting compatible with every locally
finite-type base change. -/
@[stacks 0F99] #check
  (AlgebraicGeometry.Scheme.existsUnitSplitting :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (delta : S → ℤ) [IsDimensionFunction delta]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (s : L.sections),
      ∃ C : AlgebraicGeometry.Scheme.TensorSectionSplitting
          (𝟙_ X.left.Modules) L
          (AlgebraicGeometry.Scheme.Modules.unitTensorSection L s),
        ∃ e : C.baseZero ≅ AlgebraicGeometry.Scheme.zeroScheme L s,
          e.hom ≫ AlgebraicGeometry.Scheme.zeroSchemeι L s = C.baseι ∧
            ∀ {Y : Scheme.{u}} (f : Y ⟶ X.left) [LocallyOfFiniteType f],
              ∃ C' : AlgebraicGeometry.Scheme.TensorSectionSplitting
                ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
                  (𝟙_ X.left.Modules))
                ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)
                (AlgebraicGeometry.Scheme.Modules.pullbackTensorSection f
                  (AlgebraicGeometry.Scheme.Modules.unitTensorSection L s)),
                ∃ B : C.BaseChange f C',
                  ∃ e' : C'.baseZero ≅ AlgebraicGeometry.Scheme.zeroScheme
                      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)
                      (AlgebraicGeometry.Scheme.Modules.sectionsPullback f L s),
                    e'.hom ≫ AlgebraicGeometry.Scheme.zeroSchemeι
                        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)
                        (AlgebraicGeometry.Scheme.Modules.sectionsPullback f L s) =
                      C'.baseι)

/- Lemma 42.32.7 (2): flat pullback along the transported first projection is
injective in every degree. -/
@[stacks 0F99] #check
  (AlgebraicGeometry.ChowGroup.TensorSectionSplitting.unitProjectionPullback_injective :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (delta : S → ℤ) [IsDimensionFunction delta]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (s : L.sections)
      (C : AlgebraicGeometry.Scheme.TensorSectionSplitting
        (𝟙_ X.left.Modules) L
        (AlgebraicGeometry.Scheme.Modules.unitTensorSection L s))
      (e : C.baseZero ≅ AlgebraicGeometry.Scheme.zeroScheme L s)
      (h_e : e.hom ≫ AlgebraicGeometry.Scheme.zeroSchemeι L s = C.baseι)
      (k : ℤ),
      Function.Injective
        (AlgebraicGeometry.ChowGroup.TensorSectionSplitting.unitProjectionPullback
          delta X L s C e h_e k))

/- Lemma 42.32.7 (3): the first factor zero scheme is compatibly the zero
scheme of a global section of the structure module of the total scheme. -/
@[stacks 0F99] #check
  (AlgebraicGeometry.Scheme.TensorSectionSplitting.existsFirstStructureZeroScheme :
    ∀ {Y : Scheme.{u}} (L : Y.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L] (s : L.sections)
      (C : AlgebraicGeometry.Scheme.TensorSectionSplitting
        (𝟙_ Y.Modules) L
        (AlgebraicGeometry.Scheme.Modules.unitTensorSection L s)),
      ∃ e' : C.zero₁ ≅ AlgebraicGeometry.Scheme.zeroScheme
          (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules)
          (AlgebraicGeometry.Scheme.TensorSectionSplitting.firstStructureSection C),
        e'.hom ≫ AlgebraicGeometry.Scheme.zeroSchemeι
            (SheafOfModules.unit C.L.ringCatSheaf : C.L.Modules)
            (AlgebraicGeometry.Scheme.TensorSectionSplitting.firstStructureSection C) =
          C.ι₁)

/- Lemma 42.32.7 (4): Gysin pullback commutes with flat pullback in the
unit-factor splitting square. -/
@[stacks 0F99] #check
  (AlgebraicGeometry.ChowGroup.TensorSectionSplitting.gysin_unitProjectionPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (delta : S → ℤ) [IsDimensionFunction delta]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (s : L.sections)
      (C : AlgebraicGeometry.Scheme.TensorSectionSplitting
        (𝟙_ X.left.Modules) L
        (AlgebraicGeometry.Scheme.Modules.unitTensorSection L s))
      (e : C.baseZero ≅ AlgebraicGeometry.Scheme.zeroScheme L s)
      (h_e : e.hom ≫ AlgebraicGeometry.Scheme.zeroSchemeι L s = C.baseι)
      (k : ℤ) (alpha : AlgebraicGeometry.RelativeChow delta X k),
      AlgebraicGeometry.ChowGroup.TensorSectionSplitting.firstGysin
          delta X C k
          (AlgebraicGeometry.ChowGroup.TensorSectionSplitting.projectionPullback
            delta X C k alpha) =
        AlgebraicGeometry.ChowGroup.TensorSectionSplitting.unitProjectionPullback
          delta X L s C e h_e k
          (AlgebraicGeometry.ChowGroup.gysin delta X L s k alpha))
