/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Situation_69_16_1_Cohomology

/-!
# Cohomology of higher direct images on affine étale objects

For a quasi-compact and quasi-separated morphism of algebraic spaces, étale
cohomology of a quasi-coherent module on `V ×_Y X` agrees with degree-zero
objectwise cohomology of `R^q f_* F` at an affine object `V` of `Y_étale`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Étale cohomology of an `𝒪_X`-module on the fibre product of an object of `Y_étale` with `X`. -/
abbrev cohomologyOnEtalePullback (f : X ⟶ Y) (F : X.Modules) (V : smallEtaleSite Y) (q : ℕ)
    [HasSheafify (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  AlgebraicSpace.cohomology (Limits.pullback V.hom f) (restrict F (Limits.pullback.snd V.hom f)) q

/-- Degree-zero objectwise cohomology of a higher direct image at an object of `Y_étale`. -/
abbrev higherDirectImage_degreeZero_cohomology (f : X ⟶ Y) (F : X.Modules)
    (V : smallEtaleSite Y) (q : ℕ)
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  Sheaf.H' ((SheafOfModules.toSheaf (structureSheaf Y)).obj (higherDirectImage f F q)) 0 V

/-- Lemma 69.3.2: let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-separated and
quasi-compact morphism of algebraic spaces over `S`. For any quasi-coherent
`𝒪_X`-module `F` and any affine object `V` of `Y_étale`, the groups
`cohomology (Limits.pullback V.hom f) (restrict F (Limits.pullback.snd V.hom f)) q` and
`Sheaf.H' ((SheafOfModules.toSheaf (structureSheaf Y)).obj (higherDirectImage f F q)) 0 V`
are isomorphic for all `q : ℕ`. Negative-degree cohomology and higher direct
images vanish, recovering the source quantification `q ∈ ℤ`. -/
@[stacks 08EX]
theorem cohomology_iso_higherDirectImage_degreeZero (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsQuasicoherent]
    (V : smallEtaleSite Y) [AlgebraicGeometry.IsAffine V.left.left] (q : ℕ)
    [HasSheafify (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u})]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})] :
    IsIsomorphic (cohomologyOnEtalePullback f F V q)
      (higherDirectImage_degreeZero_cohomology f F V q) :=
  sorry

/-- Degree-zero objectwise cohomology of a higher direct image is isomorphic to its
module of sections over `V`, forgotten to abelian groups. -/
theorem higherDirectImage_degreeZero_cohomology_eq_sections (f : X ⟶ Y)
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) (V : smallEtaleSite Y) (q : ℕ)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})] :
    IsIsomorphic (higherDirectImage_degreeZero_cohomology f F V q)
      ((forget₂ (ModuleCat ((structureSheaf Y).obj.obj (op V))) AddCommGrpCat.{u}).obj
        ((SheafOfModules.evaluation (structureSheaf Y) (op V)).obj
          (higherDirectImage f F q))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
