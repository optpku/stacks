module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Bimodule
public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Derived
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Linearity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal

/-!
# Relative differential graded models of derived quasi-coherent modules

A morphism `X ⟶ ofOver (Over.mk (𝟙 (Spec R)))` makes complexes of `𝒪_X`-modules
`R`-linear. This file records the resulting endomorphism differential graded
algebras, cross-Hom bimodules, and canonical derived-Hom functors.
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

/-- A complex with quasi-coherent homology represents a derived module with
quasi-coherent cohomology. -/
theorem generatorObject_mem (K : CochainComplex (Modules X) ℤ)
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)) :
    derivedQuasiCoherentModuleProperty X (DerivedCategory.Q.obj K) := sorry

/-- The derived quasi-coherent module represented by a complex with quasi-coherent homology. -/
noncomputable def generatorObject (K : CochainComplex (Modules X) ℤ)
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)) : DerivedQCoh X :=
  ⟨DerivedCategory.Q.obj K, generatorObject_mem K hKqc⟩

/-- The underlying derived module of `generatorObject K hKqc` is represented by `K`. -/
@[simp]
theorem generatorObject_obj (K : CochainComplex (Modules X) ℤ)
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n)) :
    (generatorObject K hKqc).obj = DerivedCategory.Q.obj K := sorry

/-- Enriched Hom from a complex of module sheaves admits a total right-derived functor
with values in right modules over its relative endomorphism algebra. -/
theorem hasDerivedFunctor
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) :
    @DifferentialGradedCategory.Representable.HasDerivedFunctor R _ _ (dgCategory f) K
      (@CategoryTheory.CochainComplex.Enriched.Over.quasiIso R _ (Modules X) _ _
        (moduleLinear f)) := sorry

/-- Derived enriched Hom from `K`, restricted to derived modules with quasi-coherent
cohomology, with its canonical right endomorphism-algebra action. -/
noncomputable def functor
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) :
    DerivedQCoh X ⥤ DifferentialGradedModule.Derived.Category.{u, u + 1}
      (endomorphismDGA f K) :=
  DerivedQCoh.inclusion X ⋙
    @DifferentialGradedCategory.Representable.derivedFunctor R _ _ (dgCategory f)
      (ModuleDerived X) _ K
      (@CategoryTheory.CochainComplex.Enriched.Over.derivedQ R _ (Modules X) _ _
        (moduleLinear f) _)
      (@CategoryTheory.CochainComplex.Enriched.Over.quasiIso R _ (Modules X) _ _
        (moduleLinear f))
      (@CategoryTheory.CochainComplex.Enriched.Over.derivedQIsLocalization R _ (Modules X)
        _ _ (moduleLinear f) _)
      (hasDerivedFunctor f K)

/-- On a K-injective target, derived enriched Hom is represented by the cross-Hom
right module over the endomorphism algebra of the source complex. -/
theorem functor_obj_of_kInjective
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ) [L.IsKInjective]
    (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n)) :
    Nonempty ((functor f K).obj (generatorObject L hLqc) ≅
      (DifferentialGradedModule.Derived.fromModules (endomorphismDGA f K)).obj
        (bimodule f K L).toRightModule) := sorry

/-- Derived enriched Hom is linear for the scalar action induced by the structure morphism. -/
theorem functor_linear
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) :
    @Functor.Linear R _ _ _ _ _ _ _ (derivedQCohLinear f) _ (functor f K) := sorry

/-- Derived enriched Hom on quasi-coherent derived modules admits a triangulated structure. -/
theorem functor_hasTriangulatedStructure
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) :
    (functor f K).HasTriangulatedStructure := sorry

/-- A K-injective perfect weak generator on a quasi-compact quasi-separated algebraic
space gives an equivalence by derived enriched Hom. -/
theorem functor_isEquivalence
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K : CochainComplex (Modules X) ℤ) [K.IsKInjective]
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
    (hKPerfect : ModuleDerived.IsPerfect (generatorObject K hKqc).obj)
    (hKGenerator : IsWeakGenerator (generatorObject K hKqc)) :
    (functor f K).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel
