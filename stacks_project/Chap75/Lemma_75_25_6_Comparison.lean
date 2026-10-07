module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_8_4_Linear
public import stacks_project.Chap75.Lemma_75_11_3_Associated
public import stacks_project.Chap75.Lemma_75_19_1_Instances

/-!
# Associated modules and sequential inverse limits on algebraic spaces

This file constructs the canonical comparison from the associated module of a sequential
inverse limit to the quasicoherent coreflection of the inverse limit of the associated
modules, for an algebraic space over an affine base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated

variable {R : Type u} [CommRing R]
variable {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- The functor sending an `R`-module to the associated `𝒪_X`-module `𝒪_X ⊗_R -`,
obtained by extending scalars along the structure morphism and applying `tensorOXFunctor`. -/
noncomputable def associatedFunctor
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    ModuleCat.{u} R ⥤ Modules X :=
  ModuleCat.extendScalars (Hom.globalSectionsMap f) ⋙ tensorOXFunctor X

/-- On objects, `associatedFunctor f` is `tensorOX` after extension of scalars along
`Hom.globalSectionsMap f`. -/
theorem associatedFunctor_obj
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) :
    (associatedFunctor f).obj N =
      tensorOX X ((ModuleCat.extendScalars (Hom.globalSectionsMap f)).obj N) :=
  sorry

/-- The associated `𝒪_X`-module of `N`, placed in degree zero, has quasicoherent cohomology. -/
theorem single_mem
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
        ((associatedFunctor f).obj N)) :=
  sorry

/-- The associated `𝒪_X`-module of `N`, regarded as a degree-zero object of `DerivedQCoh X`. -/
noncomputable def single
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) : DerivedQCoh X :=
  ⟨(DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj ((associatedFunctor f).obj N),
    single_mem f N⟩

/-- The underlying derived object of `single f N` is the associated `𝒪_X`-module placed in
degree zero. -/
theorem single_obj
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) :
    (single f N).obj =
      (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj ((associatedFunctor f).obj N) :=
  sorry

/-- The adjunct of the degree-zero image of the canonical map from the associated module of an
inverse limit to the inverse limit of the associated modules. -/
noncomputable def limitComparison
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [FinitePresentation f] (M : SequentialInverseSystem (ModuleCat.{u} R)) :
    single f (limit M) ⟶
      (inclusion X).rightAdjoint.obj
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
          (limit (M ⋙ associatedFunctor f))) :=
  (Adjunction.ofIsLeftAdjoint (inclusion X)).homEquiv
    (single f (limit M))
    ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
      (limit (M ⋙ associatedFunctor f)))
    ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map
      (limit.post M (associatedFunctor f)))

/-- Under the inclusion–coreflector adjunction, `limitComparison f M` corresponds to the
degree-zero image of the canonical map from the associated module of the limit. -/
theorem limitComparison_adjunct
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [FinitePresentation f] (M : SequentialInverseSystem (ModuleCat.{u} R)) :
    ((Adjunction.ofIsLeftAdjoint (inclusion X)).homEquiv
        (single f (limit M))
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
          (limit (M ⋙ associatedFunctor f)))).symm
      (limitComparison f M) =
      (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map
        (limit.post M (associatedFunctor f)) :=
  sorry

/-- For a proper, flat, finitely presented morphism to an affine scheme and a sequential inverse
system of modules with epimorphic transitions, the associated-module limit comparison is an
isomorphism. -/
theorem limitComparison_isIso
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f] [FinitePresentation f]
    (M : SequentialInverseSystem (ModuleCat.{u} R))
    [∀ n : ℕ, Epi (SequentialInverseSystem.transitionMap M (Nat.le_succ n))] :
    IsIso (limitComparison f M) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated
