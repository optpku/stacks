/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Bimodule
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom.Over
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_8_4_Linear

/-!
# Relative differential graded models of derived quasi-coherent modules

A morphism `X ⟶ ofOver (Over.mk (𝟙 (Spec R)))` makes complexes of `𝒪_X`-modules
`R`-linear. This file records the resulting endomorphism differential graded
algebras, cross-Hom bimodules, and explicit generator-model data.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel

variable {R : Type u} [CommRing R] {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- The `R`-linear structure on `𝒪_X`-modules induced by a structure morphism
`X ⟶ ofOver (Over.mk (𝟙 (Spec R)))`. -/
abbrev moduleLinear (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    Linear R (Modules X) :=
  Modules.baseLinear f

/-- The scalar structure `moduleLinear f` is the chartwise center action of `f`. -/
theorem moduleLinear_def (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    moduleLinear f = Modules.baseLinear f := sorry

/-- The `R`-linear differential graded category of complexes of `𝒪_X`-modules induced
by a structure morphism over `Spec R`. -/
@[reducible]
noncomputable def dgCategory (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    DifferentialGradedCategory R (CochainComplex (Modules X) ℤ) :=
  @CochainComplex.differentialGradedCategory (Modules X) _ _ R _ (moduleLinear f)

/-- Homogeneous morphisms in `dgCategory f` are homogeneous cochains. -/
theorem dgCategory_hom (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ) (n : ℤ) :
    (dgCategory f).Hom K L n = CochainComplex.HomComplex.Cochain K L n := sorry

/-- The endomorphism differential graded algebra over `R` of a complex of `𝒪_X`-modules,
using the enrichment induced by a structure morphism over `Spec R`. -/
noncomputable def endomorphismDGA
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) : CochainDGAlgebra.{u, u + 1} R :=
  @DifferentialGradedCategory.endomorphismDGA R _ _ (dgCategory f) K

/-- Degree `n` of `endomorphismDGA f K` is the degree-`n` homogeneous endomorphism module
of `K` in the relative enrichment. -/
theorem endomorphismDGA_X
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) (n : ℤ) :
    (endomorphismDGA f K).X n =
      @DifferentialGradedCategory.homComponent R _ _ (dgCategory f) K K n := sorry

/-- The relative cross-Hom complex `Hom(K, L)`, with its left `End_R(L)`-action and right
`End_R(K)`-action. -/
noncomputable def bimodule
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ) :
    DifferentialGradedBimodule (endomorphismDGA f L) (endomorphismDGA f K) :=
  @DifferentialGradedCategory.HomComplex.bimodule R _ _ (dgCategory f) K L

/-- Degree `n` of `bimodule f K L` is the degree-`n` relative homogeneous Hom module. -/
theorem bimodule_X
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ) (n : ℤ) :
    (bimodule f K L).X n =
      @DifferentialGradedCategory.homComponent R _ _ (dgCategory f) K L n := sorry

/-- The `R`-linear structure on derived `𝒪_X`-modules with quasi-coherent cohomology
induced by a structure morphism over `Spec R`. -/
@[reducible]
noncomputable def derivedQCohLinear
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    Linear R (DerivedQCoh X) :=
  @CategoryTheory.Linear.fullSubcategory (ModuleDerived X) _ _ R _
    (@DerivedCategory.instLinear R _ (Modules X) _ _ (moduleLinear f) _)
    (derivedQuasiCoherentModuleProperty X)

/-- The relative scalar structure on derived modules with quasi-coherent cohomology is the
full-subcategory structure induced from the derived category of `R`-linear `𝒪_X`-modules. -/
theorem derivedQCohLinear_def
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    derivedQCohLinear f =
      @CategoryTheory.Linear.fullSubcategory (ModuleDerived X) _ _ R _
        (@DerivedCategory.instLinear R _ (Modules X) _ _ (moduleLinear f) _)
        (derivedQuasiCoherentModuleProperty X) := sorry

/-- Canonical shifts on `D(𝒪_X)` restrict to derived modules with quasi-coherent cohomology. -/
noncomputable instance derivedQCohHasShift (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    HasShift (DerivedQCoh X) ℤ :=
  ObjectProperty.hasShift (derivedQuasiCoherentModuleProperty X)

variable (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
variable (K : CochainComplex (Modules X) ℤ) [K.IsKInjective]

/-- The object with quasi-coherent cohomology canonically represented by a complex with
quasi-coherent homology. -/
noncomputable def generatorObject
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)) : DerivedQCoh X :=
  ⟨DerivedCategory.Q.obj K, sorry⟩

/-- The underlying derived module of `generatorObject K hKqc` is represented by `K`. -/
@[simp]
theorem generatorObject_obj
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)) :
    (generatorObject K hKqc).obj = DerivedCategory.Q.obj K := sorry

/-- An explicit `R`-linear model of derived modules with quasi-coherent cohomology arising from
the relative endomorphism algebra of a K-injective complex. Its regular-object identification
intertwines every graded endomorphism action with the canonical action on the complex. -/
structure GeneratorModel
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)) where
  /-- The functor from modules over the relative endomorphism algebra to derived modules with
  quasi-coherent cohomology. -/
  functor : CategoryTheory.Functor
    (DifferentialGradedModule.Derived.Category (endomorphismDGA f K)) (DerivedQCoh X)
  /-- The model functor is an equivalence. -/
  isEquivalence : functor.IsEquivalence
  /-- The model functor commutes with shifts. -/
  commShift : functor.CommShift ℤ
  /-- The model functor is triangulated. -/
  isTriangulated : functor.IsTriangulated
  /-- The model functor is linear for the scalar action induced by `f`. -/
  linear : @Functor.Linear R _ _ _ _ _ _ _ _ (derivedQCohLinear f) functor
  /-- The relative regular module is carried to the object represented by `K`. -/
  regularIso :
    functor.obj (DifferentialGradedModule.Derived.regularObject (endomorphismDGA f K)) ≅
      generatorObject K hKqc
  /-- The functor identifies the full graded action of the relative endomorphism algebra on its
  regular module with the canonical derived endomorphism action on `K`. -/
  regularAction (n : ℤ) (x : (endomorphismDGA f K).homology n) :
    ShiftedHom.map
        (@Functor.shiftedHomMap _ _ _ _ _ _ functor commShift _ _ _ _
          regularIso regularIso n
          (DifferentialGradedModule.Derived.regularSelfExtLinearMap
            (endomorphismDGA f K) n x))
        (DerivedQCoh.inclusion X) =
      @CategoryTheory.CochainComplex.Enriched.Over.RHom.derivedHomOfHomology
        R _ _ _ _ (moduleLinear f) _ K K n x

namespace GeneratorModel

/-- Construct a generator model from its functor and all of its compatibility data. -/
noncomputable def of
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
    (F : CategoryTheory.Functor
      (DifferentialGradedModule.Derived.Category (endomorphismDGA f K)) (DerivedQCoh X))
    (hEquivalence : F.IsEquivalence) (hCommShift : F.CommShift ℤ)
    (hTriangulated : F.IsTriangulated)
    (hLinear : @Functor.Linear R _ _ _ _ _ _ _ _ (derivedQCohLinear f) F)
    (hRegular :
      F.obj (DifferentialGradedModule.Derived.regularObject (endomorphismDGA f K)) ≅
        generatorObject K hKqc)
    (hRegularAction : ∀ (n : ℤ) (x : (endomorphismDGA f K).homology n),
      ShiftedHom.map
          (@Functor.shiftedHomMap _ _ _ _ _ _ F hCommShift _ _ _ _
            hRegular hRegular n
            (DifferentialGradedModule.Derived.regularSelfExtLinearMap
              (endomorphismDGA f K) n x))
          (DerivedQCoh.inclusion X) =
        @CategoryTheory.CochainComplex.Enriched.Over.RHom.derivedHomOfHomology
          R _ _ _ _ (moduleLinear f) _ K K n x) :
    GeneratorModel f K hKqc where
  functor := F
  isEquivalence := hEquivalence
  commShift := hCommShift
  isTriangulated := hTriangulated
  linear := hLinear
  regularIso := hRegular
  regularAction := hRegularAction

/-- The equivalence, shift, triangulated, linear, regular-object, and regular-action conditions
of an `R`-linear generator model. -/
theorem spec {hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)}
    (M : GeneratorModel f K hKqc) :
    M.functor.IsEquivalence ∧
      Nonempty (M.functor.CommShift ℤ) ∧
      M.functor.IsTriangulatedWith M.commShift ∧
      @Functor.Linear R _ _ _ _ _ _ _ _ (derivedQCohLinear f) M.functor ∧
      Nonempty
        (M.functor.obj
            (DifferentialGradedModule.Derived.regularObject (endomorphismDGA f K)) ≅
          generatorObject K hKqc) ∧
      ∀ (n : ℤ) (x : (endomorphismDGA f K).homology n),
        ShiftedHom.map
            (@Functor.shiftedHomMap _ _ _ _ _ _ M.functor M.commShift _ _ _ _
              M.regularIso M.regularIso n
              (DifferentialGradedModule.Derived.regularSelfExtLinearMap
                (endomorphismDGA f K) n x))
            (DerivedQCoh.inclusion X) =
          @CategoryTheory.CochainComplex.Enriched.Over.RHom.derivedHomOfHomology
            R _ _ _ _ (moduleLinear f) _ K K n x := sorry

end GeneratorModel

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel
