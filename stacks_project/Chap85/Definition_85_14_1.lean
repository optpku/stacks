/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Definition_85_14_1_Ringed
public import stacks_project.Chap85.Definition_85_14_1_System

/-!
# Definition 85.14.1

In Situation 85.3.3, with a sheaf of rings `O` on `C_total`, a simplicial system
of the derived category of modules consists of objects `K_n` of `D(O_n)` and maps
`K_φ : Lf_φ^* K_m ⟶ K_n` in `D(O_n)` for `φ : m ⟶ n`, subject to
`K_{φ ∘ ψ} = K_φ ∘ Lf_φ^* K_ψ` after `Lf_{φ ∘ ψ}^* = Lf_φ^* ∘ Lf_ψ^*`.
The system is cartesian when every `K_φ` is an isomorphism. Morphisms are the
obvious stagewise natural maps.
-/

@[expose] public section

open CategoryTheory
open RingedSite (ToposHom)

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (X : SimplexCategory → RingedSite.{u, v, w})
variable [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fHom φ)]
variable [HasModulePullbackFunctoriality X fHom]

/-- Definition 85.14.1 (1)
In Situation 85.3.3, let `O` be a sheaf of rings on `C_total`. A simplicial
system of the derived category of modules, on a family of component ringed
topoi `X n` with morphisms `f_φ : ToposHom (X n) (X m)` of ringed topoi, consists
of objects `K_n` of `D(O_n)` and maps `K_φ : Lf_φ^* K_m ⟶ K_n` in `D(O_n)` for
`φ : m ⟶ n`, subject to `K_{φ ∘ ψ} = K_φ ∘ Lf_φ^* K_ψ` after the canonical
identification `Lf_{φ ∘ ψ}^* = Lf_φ^* ∘ Lf_ψ^*`. -/
@[stacks 0D9N]
abbrev DerivedCategoryModuleSystem :=
  DerivedModuleSystem X fHom

/-- The source-facing system type is the derived-module system on a family of component
ringed topoi. -/
theorem DerivedCategoryModuleSystem_eq :
    DerivedCategoryModuleSystem X fHom = DerivedModuleSystem X fHom :=
  sorry

/-- Definition 85.14.1 (2)
In Situation 85.3.3, a simplicial system of the derived category of modules is
cartesian if every `K_φ` is an isomorphism in `D(O_n)`. -/
@[stacks 0D9N]
abbrev DerivedCategoryModuleSystem.IsCartesian
    (K : DerivedCategoryModuleSystem X fHom) :=
  DerivedModuleSystem.IsCartesian K

/-- Cartesianness of a derived-module system is equivalent to every transition being an
isomorphism. -/
theorem DerivedCategoryModuleSystem.isCartesian_iff
    (K : DerivedCategoryModuleSystem X fHom) :
    DerivedCategoryModuleSystem.IsCartesian X fHom K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ) :=
  sorry

/-- Definition 85.14.1 (3)
Given two simplicial systems of the derived category of modules, a morphism is a
family `α_n : K_n ⟶ L_n` in `D(O_n)` natural for the transitions `K_φ`. -/
@[stacks 0D9N]
abbrev DerivedCategoryModuleSystem.Hom
    (K L : DerivedCategoryModuleSystem X fHom) :=
  DerivedModuleSystem.Hom K L

/-- A morphism of derived-module systems is natural for the transitions `K_φ`. -/
theorem DerivedCategoryModuleSystem.hom_naturality
    {K L : DerivedCategoryModuleSystem X fHom}
    (α : DerivedCategoryModuleSystem.Hom X fHom K L)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    K.map φ ≫ α.app n =
      (fHom φ).modulePullbackDerived.map (α.app m) ≫ L.map φ :=
  sorry

end CategoryTheory.SimplicialSites
