module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Bimodule
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom.Over
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Shift
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence

/-!
# Relative Differential Graded Models of Derived Quasicoherent Modules

A morphism `X ⟶ Spec R` makes complexes of `𝒪_X`-modules `R`-linear. This file records
the resulting endomorphism differential graded algebras, cross-Hom bimodules, and explicit
generator-model data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The `R`-linear structure on `𝒪_X`-modules induced by a structure morphism
`X ⟶ Spec R`. -/
@[reducible]
noncomputable def moduleLinear (f : X ⟶ Spec (CommRingCat.of R)) :
    Linear R X.toRingedSpace.Modules :=
  Linear.ofRingMorphism
    ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
      (Scheme.Hom.globalSectionsMap f))

/-- The scalar structure `moduleLinear f` is induced by the global-sections map of `f`. -/
theorem moduleLinear_def (f : X ⟶ Spec (CommRingCat.of R)) :
    moduleLinear f =
      Linear.ofRingMorphism
        ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
          (Scheme.Hom.globalSectionsMap f)) := sorry

/-- The `R`-linear differential graded category of complexes of `𝒪_X`-modules induced
by `f : X ⟶ Spec R`. -/
@[reducible]
noncomputable def dgCategory (f : X ⟶ Spec (CommRingCat.of R)) :
    DifferentialGradedCategory R (CochainComplex X.toRingedSpace.Modules ℤ) :=
  @CochainComplex.differentialGradedCategory
    X.toRingedSpace.Modules _ _ R _ (moduleLinear f)

/-- Homogeneous morphisms in `dgCategory f` are homogeneous cochains. -/
theorem dgCategory_hom (f : X ⟶ Spec (CommRingCat.of R))
    (K L : CochainComplex X.toRingedSpace.Modules ℤ) (n : ℤ) :
    (dgCategory f).Hom K L n = CochainComplex.HomComplex.Cochain K L n := sorry

/-- The endomorphism differential graded algebra over `R` of a complex of `𝒪_X`-modules,
using the enrichment induced by `f : X ⟶ Spec R`. -/
noncomputable def endomorphismDGA (f : X ⟶ Spec (CommRingCat.of R))
    (K : CochainComplex X.toRingedSpace.Modules ℤ) : CochainDGAlgebra.{u, u} R :=
  @DifferentialGradedCategory.endomorphismDGA R _ _ (dgCategory f) K

/-- Degree `n` of `endomorphismDGA f K` is the degree-`n` homogeneous endomorphism module
of `K` in the relative enrichment. -/
theorem endomorphismDGA_X (f : X ⟶ Spec (CommRingCat.of R))
    (K : CochainComplex X.toRingedSpace.Modules ℤ) (n : ℤ) :
    (endomorphismDGA f K).X n =
      @DifferentialGradedCategory.homComponent R _ _ (dgCategory f) K K n := sorry

/-- The relative cross-Hom complex `Hom(K, L)`, with its left `End_R(L)`-action and right
`End_R(K)`-action. -/
noncomputable def bimodule (f : X ⟶ Spec (CommRingCat.of R))
    (K L : CochainComplex X.toRingedSpace.Modules ℤ) :
    DifferentialGradedBimodule (endomorphismDGA f L) (endomorphismDGA f K) :=
  @DifferentialGradedCategory.HomComplex.bimodule R _ _ (dgCategory f) K L

/-- Degree `n` of `bimodule f K L` is the degree-`n` relative homogeneous Hom module. -/
theorem bimodule_X (f : X ⟶ Spec (CommRingCat.of R))
    (K L : CochainComplex X.toRingedSpace.Modules ℤ) (n : ℤ) :
    (bimodule f K L).X n =
      @DifferentialGradedCategory.homComponent R _ _ (dgCategory f) K L n := sorry

/-- The `R`-linear structure on derived `𝒪_X`-modules with quasicoherent cohomology
induced by `f : X ⟶ Spec R`. -/
@[reducible]
noncomputable def derivedQCohLinear (f : X ⟶ Spec (CommRingCat.of R)) :
    Linear R (Scheme.ModuleDerived.Quasicoherent X) :=
  @CategoryTheory.Linear.fullSubcategory
    (RingedSpace.ModuleDerived X.toRingedSpace) _ _ R _
    (@DerivedCategory.instLinear R _ X.toRingedSpace.Modules _ _ (moduleLinear f) _)
    (Scheme.ModuleDerived.quasicoherentProperty X)

/-- The relative scalar structure on derived modules with quasicoherent cohomology is the
full-subcategory structure induced from the derived category of `R`-linear `𝒪_X`-modules. -/
theorem derivedQCohLinear_def (f : X ⟶ Spec (CommRingCat.of R)) :
    derivedQCohLinear f =
      @CategoryTheory.Linear.fullSubcategory
        (RingedSpace.ModuleDerived X.toRingedSpace) _ _ R _
        (@DerivedCategory.instLinear R _ X.toRingedSpace.Modules _ _ (moduleLinear f) _)
        (Scheme.ModuleDerived.quasicoherentProperty X) := sorry

variable (f : X ⟶ Spec (CommRingCat.of R))
variable (K : CochainComplex X.toRingedSpace.Modules ℤ) [K.IsKInjective]

/-- The object with quasicoherent cohomology canonically represented by a complex with
quasicoherent homology. -/
noncomputable def generatorObject
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n)) : Scheme.ModuleDerived.Quasicoherent X :=
  ⟨DerivedCategory.Q.obj K, sorry⟩

/-- The underlying derived module of `generatorObject K hKqc` is represented by `K`. -/
@[simp]
theorem generatorObject_obj
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n)) :
    (generatorObject K hKqc).obj = DerivedCategory.Q.obj K := sorry

/-- An explicit `R`-linear model of derived modules with quasicoherent cohomology arising from
the relative endomorphism algebra of a K-injective complex. Its regular-object identification
intertwines every graded endomorphism action with the canonical action on the complex. -/
structure GeneratorModel
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n)) where
  /-- The functor from modules over the relative endomorphism algebra to derived modules with
  quasicoherent cohomology. -/
  functor : CategoryTheory.Functor
    (DifferentialGradedModule.Derived.Category (endomorphismDGA f K))
      (Scheme.ModuleDerived.Quasicoherent X)
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
        (Scheme.ModuleDerived.Quasicoherent.inclusion X) =
      @CategoryTheory.CochainComplex.Enriched.Over.RHom.derivedHomOfHomology
        R _ _ _ _ (moduleLinear f) _ K K n x

namespace GeneratorModel

/-- Construct a generator model from its functor and all of its compatibility data. -/
noncomputable def of
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (F : CategoryTheory.Functor
      (DifferentialGradedModule.Derived.Category (endomorphismDGA f K))
        (Scheme.ModuleDerived.Quasicoherent X))
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
          (Scheme.ModuleDerived.Quasicoherent.inclusion X) =
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
theorem spec
    {hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n)} (M : GeneratorModel f K hKqc) :
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
            (Scheme.ModuleDerived.Quasicoherent.inclusion X) =
          @CategoryTheory.CochainComplex.Enriched.Over.RHom.derivedHomOfHomology
            R _ _ _ _ (moduleLinear f) _ K K n x := sorry

end GeneratorModel

end AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel
