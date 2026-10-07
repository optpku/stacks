module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport

/-!
# Derived modules supported on a subset

A derived `𝒪_X`-module is supported on a subset `T ⊆ Points X` when every
cohomology sheaf is supported on `T`. This is the algebraic-space specialization of
`DerivedCategory.cohomologyIn`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The object property of `𝒪_X`-modules whose support is contained in `T`. -/
abbrev moduleSupportedOn (T : Set (Points X)) : ObjectProperty X.Modules :=
  fun F ↦ moduleSupport F ⊆ T

/-- Membership in `moduleSupportedOn T` is support containment in `T`. -/
theorem mem_moduleSupportedOn_iff (T : Set (Points X)) (F : X.Modules) :
    moduleSupportedOn T F ↔ moduleSupport F ⊆ T := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Derived `𝒪_X`-modules whose cohomology sheaves are all supported on `T`. -/
abbrev supportedOn (T : Set (Points X)) : ObjectProperty (ModuleDerived X) :=
  DerivedCategory.cohomologyIn (Modules.moduleSupportedOn T)

/-- A derived `𝒪_X`-module is supported on `T` when each of its cohomology sheaves is. -/
abbrev IsSupportedOn (K : ModuleDerived X) (T : Set (Points X)) : Prop :=
  supportedOn T K

/-- The full subcategory of derived `𝒪_X`-modules supported on `T`. -/
abbrev SupportedOn (T : Set (Points X)) :=
  (supportedOn T).FullSubcategory

namespace SupportedOn

/-- The inclusion of derived `𝒪_X`-modules supported on `T` into all derived modules. -/
abbrev inclusion (T : Set (Points X)) : SupportedOn T ⥤ ModuleDerived X :=
  (supportedOn T).ι

end SupportedOn

/-- The derived support condition is the corresponding degreewise cohomology condition. -/
theorem isSupportedOn_iff (K : ModuleDerived X) (T : Set (Points X)) :
    IsSupportedOn K T ↔
      ∀ i : ℤ, Modules.moduleSupportedOn T
        ((DerivedCategory.homologyFunctor (Modules X) i).obj K) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
