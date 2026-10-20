module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued Leray spectral sequences on ringed spaces

The Leray construction naturally takes values in modules over the global section ring of the
target.  This leaf retains that linear structure; the additive Leray owner is obtained only after
forgetting scalars.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleLeray.Linear

variable {X Y : RingedSpace.{u}}

/-- The condition that direct image sends injectives to bounded-below acyclic objects for
module-valued global sections. -/
@[stacks 0732 "linear Leray acyclicity condition"]
abbrev IsAcyclic (f : X ⟶ Y) : Prop :=
  ∀ (I : X.Modules) [Injective I],
    Functor.RightAcyclic.Bounded (moduleGlobalSectionsFunctor Y)
      ((RingedSpace.Hom.pushforward f).obj I)

/-- The canonical module-valued Leray realization. -/
@[stacks 0732 "module-valued Leray spectral sequence"]
abbrev Realization (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) :=
  Functor.RightDerived.Grothendieck.canonical (RingedSpace.Hom.pushforward f)
    (moduleGlobalSectionsFunctor Y) K

/-- The module-valued Leray second-page target as a functor of the derived input. -/
@[stacks 0732 "module-valued Leray page-two functor"]
noncomputable abbrev pageTwoFunctor (f : X ⟶ Y) (p : ℕ) (q : ℤ) :
    DerivedCategory.Plus X.Modules ⥤ ModuleCat (globalSectionsRing Y) :=
  Functor.RightDerived.Grothendieck.pageTwoFunctor (moduleGlobalSectionsFunctor Y)
    (moduleDerivedPushforwardPlus f) p q

/-- The `(p, q)` target of the module-valued Leray second page. -/
@[stacks 0732 "module-valued Leray page two"]
abbrev pageTwo (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules)
    (p : ℕ) (q : ℤ) : ModuleCat (globalSectionsRing Y) :=
  (pageTwoFunctor f p q).obj K

/-- The module-valued Leray abutment as a functor of the derived input. -/
@[stacks 0732 "module-valued Leray abutment functor"]
noncomputable abbrev abutmentFunctor (f : X ⟶ Y) (n : ℤ) :
    DerivedCategory.Plus X.Modules ⥤ ModuleCat (globalSectionsRing Y) :=
  Functor.RightDerived.Grothendieck.abutmentFunctor
    (Functor.RightDerived.Bounded.functor
      (RingedSpace.Hom.pushforward f ⋙ moduleGlobalSectionsFunctor Y)) n

/-- The degree-`n` target of the module-valued Leray abutment. -/
@[stacks 0732 "module-valued Leray abutment"]
abbrev abutment (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules)
    (n : ℤ) : ModuleCat (globalSectionsRing Y) :=
  (abutmentFunctor f n).obj K

/-- A map of module-valued Leray realizations over a derived morphism. -/
@[stacks 0732 "map of module-valued Leray spectral sequences"]
abbrev Map {f : X ⟶ Y} {K L : DerivedCategory.Plus X.Modules} (φ : K ⟶ L)
    (S : Realization f K) (T : Realization f L) :=
  Functor.RightDerived.Grothendieck.SpectralSequence.Map φ S T

namespace Map

export Functor.RightDerived.Grothendieck.SpectralSequence.Map
  (ext ext_filteredMap pageTwo_hom abutment_hom id comp reindex reindex_rfl
    id_comp comp_id assoc)

end Map

/-- The generic functorial Grothendieck owner specialized to module-valued Leray realizations. -/
@[stacks 0732 "functorial module-valued Leray spectral sequence"]
abbrev Functorial (f : X ⟶ Y) :=
  Functor.RightDerived.Grothendieck.SpectralSequence.Functorial
    (moduleGlobalSectionsFunctor Y) (moduleDerivedPushforwardPlus f)
    (Functor.RightDerived.Bounded.functor
      (RingedSpace.Hom.pushforward f ⋙ moduleGlobalSectionsFunctor Y))

/-- The linear Leray acyclicity condition holds for every ringed-space morphism. -/
@[stacks 0732 "linear Leray acyclicity"]
theorem isAcyclic (f : X ⟶ Y) : IsAcyclic f := sorry

/-- Every bounded-below derived module admits a module-valued Leray realization. -/
@[stacks 0732 "module-valued Leray existence"]
theorem nonempty (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) :
    Nonempty (Realization f K) := sorry

/-- Module-valued Leray realizations can be chosen functorially in the derived input. -/
@[stacks 0732 "functorial module-valued Leray existence"]
theorem functorial (f : X ⟶ Y) : Nonempty (Functorial f) := sorry

/-- A derived morphism admits compatible module-valued Leray realizations and a realization map.
-/
@[stacks 0732 "module-valued Leray map existence"]
theorem existsMap (f : X ⟶ Y) {K L : DerivedCategory.Plus X.Modules} (φ : K ⟶ L) :
    ∃ (S : Realization f K) (T : Realization f L), Nonempty (Map φ S T) := sorry

/-- The canonical linear page-two target has the usual module-cohomology presentation. -/
@[stacks 0732 "module-valued Leray page-two comparison"]
theorem pageTwo_isIsomorphic_cohomology (f : X ⟶ Y)
    (K : DerivedCategory.Plus X.Modules) (p : ℕ) (q : ℤ) :
    IsIsomorphic (pageTwo f K p q)
      (moduleCohomologyAtOpen (⊤ : Opens Y.carrier)
        (moduleDerivedPushforwardPlus.cohomology f K q) p) := sorry

end AlgebraicGeometry.RingedSpace.ModuleLeray.Linear
