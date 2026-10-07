module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Adjunction
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Injective
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.ChangeOfScalars

@[expose] public section

noncomputable section

open CategoryTheory Limits Abelian

universe u

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

variable {R G : Type u} [CommRing R] [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The small-universe Ext witness used to define the cohomology functor. -/
-- Local instance justification (search instability): the small `HasExt` witness is determined
-- by functorial injectives and must not compete globally with the instance in later files.
instance discreteModuleCatHasExt : HasExt.{u} (DiscreteModuleCat R G) :=
  hasExt_of_enoughInjectives _

/-- The `R`-module underlying continuous cohomology, represented by Ext from the trivial
regular coefficient. -/
def cohomologyObject (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) (M : DiscreteModuleCat R G) :
    ModuleCat R :=
  ModuleCat.of R (Ext (trivialCoefficient R G) M i)

/-- The cohomology map induced by an equivariant linear morphism of coefficients. -/
def cohomologyMap (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ)
    {M N : DiscreteModuleCat R G} (f : M ⟶ N) :
    cohomologyObject R G i M ⟶ cohomologyObject R G i N :=
  ModuleCat.ofHom
    ((Ext.mk₀ f).postcompOfLinear R (trivialCoefficient R G) (add_zero i))

/-- The cohomology map of an identity is an identity. -/
theorem cohomologyMap_id (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) (M : DiscreteModuleCat R G) :
    cohomologyMap R G i (𝟙 M) = 𝟙 (cohomologyObject R G i M) := sorry

/-- Cohomology maps preserve composition. -/
theorem cohomologyMap_comp (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ)
    {M N P : DiscreteModuleCat R G} (f : M ⟶ N) (g : N ⟶ P) :
    cohomologyMap R G i (f ≫ g) = cohomologyMap R G i f ≫ cohomologyMap R G i g := sorry

/-- Continuous cohomology of discrete `R`-linear `G`-modules as a module-valued functor. -/
def cohomologyFunctor (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) :
    DiscreteModuleCat R G ⥤ ModuleCat R where
  obj := cohomologyObject R G i
  map := cohomologyMap R G i
  map_id := cohomologyMap_id R G i
  map_comp := cohomologyMap_comp R G i

/-- The value of `cohomologyFunctor` is Ext from the trivial regular coefficient. -/
theorem cohomologyFunctor_obj (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) (M : DiscreteModuleCat R G) :
    (cohomologyFunctor R G i).obj M =
      ModuleCat.of R (Ext (trivialCoefficient R G) M i) := sorry

/-- The action of `cohomologyFunctor` on morphisms is Ext postcomposition. -/
theorem cohomologyFunctor_map (R G : Type u) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ)
    {M N : DiscreteModuleCat R G} (f : M ⟶ N) :
    (cohomologyFunctor R G i).map f = cohomologyMap R G i f := sorry

/-- The component of the comparison between forgetting cohomology and first forgetting the
coefficient scalars. -/
def forgetComparisonApp (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) (M : DiscreteModuleCat R G) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((cohomologyFunctor R G i).obj M) ⟶
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((cohomologyFunctor ℤ G i).obj
          ((restrictScalars (Int.castRingHom R)).obj M)) :=
  AddCommGrpCat.ofHom
    ((Adjunction.Ext.comparison (extendRestrictAdjunction (Int.castRingHom R))
      (trivialCoefficient ℤ G) M i).comp
        ((Ext.mk₀ (extendTrivialHom R G)).precomp M (zero_add i)))

/-- The comparison components are natural in the coefficient module. -/
theorem forgetComparison_naturality (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ)
    {M N : DiscreteModuleCat R G} (f : M ⟶ N) :
    (cohomologyFunctor R G i ⋙ forget₂ (ModuleCat R) AddCommGrpCat).map f ≫
      forgetComparisonApp R G i N =
      forgetComparisonApp R G i M ≫
        (restrictScalars (Int.castRingHom R) ⋙ cohomologyFunctor ℤ G i ⋙
          forget₂ (ModuleCat ℤ) AddCommGrpCat).map f := sorry

/-- The natural comparison between the two routes from discrete continuous `R`-linear
`G`-modules to abelian groups. -/
def forgetComparison (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) :
    cohomologyFunctor R G i ⋙ forget₂ (ModuleCat R) AddCommGrpCat ⟶
      restrictScalars (Int.castRingHom R) ⋙ cohomologyFunctor ℤ G i ⋙
        forget₂ (ModuleCat ℤ) AddCommGrpCat where
  app := forgetComparisonApp R G i
  naturality := fun _ _ f ↦ forgetComparison_naturality R G i f

/-- Each component of `forgetComparison` is the Ext comparison for the scalar adjunction,
precomposed by the canonical comparison on trivial coefficients. -/
theorem forgetComparison_app (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) (M : DiscreteModuleCat R G) :
    (forgetComparison R G i).app M =
      AddCommGrpCat.ofHom
        ((Adjunction.Ext.comparison (extendRestrictAdjunction (Int.castRingHom R))
          (trivialCoefficient ℤ G) M i).comp
            ((Ext.mk₀ (extendTrivialHom R G)).precomp M (zero_add i))) := sorry

/-- Forgetting the scalar structure preserves the cohomology comparison isomorphism. -/
instance instIsIsoForgetComparison (R G : Type) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (i : ℕ) :
    IsIso (forgetComparison R G i) := sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
