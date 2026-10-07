module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent

/-!
# Derived category of quasi-coherent modules on an algebraic space

`DerivedQCoh X` is the full subcategory of `D(𝒪_X)` on objects whose cohomology
sheaves are quasi-coherent.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The standard derived-category structure on `𝒪_X`-modules on an algebraic space. -/
instance modulesHasDerivedCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasDerivedCategory (Modules X) :=
  HasDerivedCategory.standard (Modules X)

/-- The unbounded derived category `D(𝒪_X)` of module sheaves on an algebraic space. -/
abbrev ModuleDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  DerivedCategory (Modules X)

/-- The property that every cohomology sheaf of a derived `𝒪_X`-module is quasi-coherent. -/
abbrev derivedQuasiCoherentModuleProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (ModuleDerived X) :=
  DerivedCategory.cohomologyIn (quasiCoherentModuleProperty X)

/-- The derived category of `𝒪_X`-modules with quasi-coherent cohomology sheaves. -/
abbrev DerivedQCoh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  DerivedCategory.CohomologyIn (quasiCoherentModuleProperty X)

namespace DerivedQCoh

/-- The inclusion of derived modules with quasi-coherent cohomology into `D(𝒪_X)`. -/
abbrev inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedQCoh X ⥤ ModuleDerived X :=
  (derivedQuasiCoherentModuleProperty X).ι

/-- An object of `D(𝒪_X)` lies in `DerivedQCoh X` iff every cohomology sheaf is
quasi-coherent. -/
theorem mem_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    derivedQuasiCoherentModuleProperty X E ↔
      ∀ n : ℤ, quasiCoherentModuleProperty X
        ((DerivedCategory.homologyFunctor (Modules X) n).obj E) := sorry

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
