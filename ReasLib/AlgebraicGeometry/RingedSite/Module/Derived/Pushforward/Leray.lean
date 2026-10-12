/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.FiniteLimits
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Acyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Leray spectral sequences for modules on ringed sites

The root owner is the canonical Grothendieck spectral sequence for direct image followed by
global sections.  Its second page and abutment retain the representation-independent generic
targets.  The `Ext` namespace and the global-abutment comparison expose the textbook
presentations only as isomorphism properties, so no noncanonical comparison is hidden in the
core data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

-- Local instance justification (defeq pin): use the standard derived-category model
-- already fixed explicitly by ModuleDerived and moduleLocalization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe z uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

section Realization

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{z}]
variable [EnoughInjectives (ModuleCat.{z} X)] [EnoughInjectives (ModuleCat.{z} Y)]

/-- The canonical Leray spectral sequence for direct image followed by global sections. -/
@[stacks 0732 "Leray spectral sequence"]
abbrev Leray (f : Hom X Y) (K : DerivedCategory.Plus (ModuleCat.{z} X)) :=
  Functor.RightDerived.Grothendieck.canonical f.modulePushforward
    (moduleGlobalSectionsAdditiveFunctor Y) K

namespace Leray

/-- The condition in the Grothendieck theorem: direct image sends injectives to objects that are
bounded-below right acyclic for global sections. -/
@[stacks 0732 "Leray acyclicity condition"]
abbrev IsAcyclic (f : Hom X Y) : Prop :=
  ∀ (I : ModuleCat.{z} X) [Injective I],
    Functor.RightAcyclic.Bounded
      (moduleGlobalSectionsAdditiveFunctor Y) (f.modulePushforward.obj I)

/-- The canonical `(p, q)` Leray second-page target as a functor of the derived input. -/
@[stacks 0732 "Leray page-two functor"]
abbrev pageTwoFunctor (f : Hom X Y) (p : ℕ) (q : ℤ) :
    DerivedCategory.Plus (ModuleCat.{z} X) ⥤ AddCommGrpCat.{z} :=
  Functor.RightDerived.Grothendieck.pageTwoFunctor
    (moduleGlobalSectionsAdditiveFunctor Y) (modulePushforwardDerivedPlus f) p q

/-- The canonical `(p, q)` target on the second page of the Leray spectral sequence. -/
@[stacks 0732 "Leray page two"]
abbrev pageTwo (f : Hom X Y) (K : DerivedCategory.Plus (ModuleCat.{z} X))
    (p : ℕ) (q : ℤ) : AddCommGrpCat.{z} :=
  (pageTwoFunctor (X := X) (Y := Y) f p q).obj K

/-- The map on canonical Leray second-page targets induced by a derived morphism. -/
@[stacks 0732 "Leray page-two naturality"]
abbrev pageTwoMap (f : Hom X Y) {K L : DerivedCategory.Plus (ModuleCat.{z} X)}
    (φ : K ⟶ L) (p : ℕ) (q : ℤ) :
    pageTwo (X := X) (Y := Y) f K p q ⟶ pageTwo (X := X) (Y := Y) f L p q :=
  (pageTwoFunctor (X := X) (Y := Y) f p q).map φ

/-- The canonical Leray abutment as a functor of the derived input. -/
@[stacks 0732 "Leray abutment functor"]
abbrev abutmentFunctor (f : Hom X Y) (n : ℤ) :
    DerivedCategory.Plus (ModuleCat.{z} X) ⥤ AddCommGrpCat.{z} :=
  Functor.RightDerived.Grothendieck.abutmentFunctor
    (Functor.RightDerived.Bounded.functor
      (f.modulePushforward ⋙ moduleGlobalSectionsAdditiveFunctor Y)) n

/-- The canonical degree-`n` abutment target of the Leray spectral sequence. -/
@[stacks 0732 "Leray abutment"]
abbrev abutment (f : Hom X Y) (K : DerivedCategory.Plus (ModuleCat.{z} X))
    (n : ℤ) : AddCommGrpCat.{z} :=
  (abutmentFunctor (X := X) (Y := Y) f n).obj K

/-- The map on canonical Leray abutment targets induced by a derived morphism. -/
@[stacks 0732 "Leray abutment naturality"]
abbrev abutmentMap (f : Hom X Y) {K L : DerivedCategory.Plus (ModuleCat.{z} X)}
    (φ : K ⟶ L) (n : ℤ) :
    abutment (X := X) (Y := Y) f K n ⟶ abutment (X := X) (Y := Y) f L n :=
  (abutmentFunctor (X := X) (Y := Y) f n).map φ

/-- A map of Leray spectral sequences over a morphism of bounded-below derived modules. -/
@[stacks 0732 "map of Leray spectral sequences"]
abbrev Map {f : Hom X Y} {K L : DerivedCategory.Plus (ModuleCat.{z} X)}
    (φ : K ⟶ L) (S : Leray (X := X) (Y := Y) f K)
    (T : Leray (X := X) (Y := Y) f L) :=
  Functor.RightDerived.Grothendieck.SpectralSequence.Map φ S T

namespace Map

export Functor.RightDerived.Grothendieck.SpectralSequence.Map
  (ext ext_filteredMap pageTwo_hom abutment_hom id comp reindex reindex_rfl
    id_comp comp_id assoc)

end Map

/-- The generic functorial Grothendieck owner specialized to Leray realizations. -/
@[stacks 0732 "functorial Leray spectral sequence"]
abbrev Functorial (f : Hom X Y) :=
  Functor.RightDerived.Grothendieck.SpectralSequence.Functorial
    (moduleGlobalSectionsAdditiveFunctor Y)
    (Functor.RightDerived.Bounded.functor f.modulePushforward)
    (Functor.RightDerived.Bounded.functor
      (f.modulePushforward ⋙ moduleGlobalSectionsAdditiveFunctor Y))

/-- A canonical Leray realization exists under the abstract Grothendieck acyclicity condition. -/
@[stacks 0732 "abstract acyclicity condition"]
theorem nonemptyOfAcyclic (f : Hom X Y) (h : IsAcyclic f)
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) :
    Nonempty (Leray (X := X) (Y := Y) f K) := sorry

/-- Under the abstract acyclicity condition, a derived morphism admits compatible Leray
realizations and a map between them. -/
@[stacks 0732 "Leray map existence under abstract acyclicity"]
theorem existsMapOfAcyclic (f : Hom X Y) (h : IsAcyclic f)
    {K L : DerivedCategory.Plus (ModuleCat.{z} X)} (φ : K ⟶ L) :
    ∃ (S : Leray (X := X) (Y := Y) f K)
      (T : Leray (X := X) (Y := Y) f L),
      Nonempty (Map (X := X) (Y := Y) φ S T) := sorry

/-- Under the abstract acyclicity condition, Leray realizations can be chosen coherently and
functorially in the bounded-below derived input. -/
@[stacks 0732 "functorial Leray realization under abstract acyclicity"]
theorem functorialOfAcyclic (f : Hom X Y) (h : IsAcyclic f) :
    Nonempty (Functorial (X := X) (Y := Y) f) := sorry

end Leray

end Realization

namespace Leray

section Acyclicity

variable [UnivLE.{max uY vY, z}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf Y.siteTopology AddCommGrpCat.{z})]

/-- The Leray acyclicity condition holds for every morphism of ringed sites. -/
@[stacks 072Z "Leray acyclicity"]
theorem isAcyclic (f : Hom X Y) : IsAcyclic f := sorry

/-- Stacks 0732: every bounded-below derived module admits a canonical Leray realization. -/
@[stacks 0732]
theorem nonempty [UnivLE.{max uX vX, z}]
    [EnoughInjectives (ModuleCat.{z} X)] [EnoughInjectives (ModuleCat.{z} Y)]
    (f : Hom X Y) (K : DerivedCategory.Plus (ModuleCat.{z} X)) :
    Nonempty (Leray (X := X) (Y := Y) f K) := sorry

/-- A derived morphism admits compatible canonical Leray realizations and a map between them. -/
@[stacks 0732 "Leray map existence"]
theorem existsMap [UnivLE.{max uX vX, z}]
    [EnoughInjectives (ModuleCat.{z} X)] [EnoughInjectives (ModuleCat.{z} Y)]
    (f : Hom X Y) {K L : DerivedCategory.Plus (ModuleCat.{z} X)} (φ : K ⟶ L) :
    ∃ (S : Leray (X := X) (Y := Y) f K)
      (T : Leray (X := X) (Y := Y) f L),
      Nonempty (Map (X := X) (Y := Y) φ S T) := sorry

/-- Leray realizations can be chosen coherently and functorially in the bounded-below derived
module. -/
@[stacks 0732 "functorial Leray realization"]
theorem functorial [UnivLE.{max uX vX, z}]
    [EnoughInjectives (ModuleCat.{z} X)] [EnoughInjectives (ModuleCat.{z} Y)]
    (f : Hom X Y) : Nonempty (Functorial (X := X) (Y := Y) f) := sorry

end Acyclicity

section GlobalAbutment

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{z}]
variable [EnoughInjectives (ModuleCat.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (moduleGlobalSectionsToDerived.{z} X) (ModuleQis.{z} X)]

/-- Derived global cohomology on `X`, functorial in a bounded-below derived module. -/
@[stacks 0732 "derived global-cohomology functor"]
abbrev globalAbutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (ModuleCat.{z} X) ⥤ AddCommGrpCat.{z} :=
  DerivedCategory.Plus.ι ⋙
    Functor.totalRightDerived (moduleGlobalSectionsToDerived.{z} X)
      (moduleLocalization.{z} X) (ModuleQis.{z} X) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{z} n

/-- The canonical composite-derived abutment is naturally isomorphic to derived global
cohomology on the source ringed site. -/
@[stacks 0732 "Leray global-abutment comparison"]
theorem abutmentFunctor_isIsomorphic (f : Hom X Y) (n : ℤ) :
    IsIsomorphic (abutmentFunctor (X := X) (Y := Y) f n)
      (globalAbutmentFunctor (X := X) n) := sorry

/-- The degree-`n` canonical Leray abutment is isomorphic to derived global cohomology on the
source ringed site. -/
@[stacks 0732 "Leray global abutment"]
theorem abutment_isIsomorphic (f : Hom X Y)
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) (n : ℤ) :
    IsIsomorphic (abutment (X := X) (Y := Y) f K n)
      ((globalAbutmentFunctor (X := X) n).obj K) := sorry

end GlobalAbutment

namespace Ext

section PageTwo

variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
variable [EnoughInjectives (ModuleCat.{w} X)] [EnoughInjectives (ModuleCat.{w} Y)]
variable [HasExt (ModuleCat.{w} Y)]

/-- The textbook `Ext` presentation of the `(p, q)` Leray target, functorial in the input. -/
@[stacks 0732 "Ext presentation of the Leray page-two functor"]
abbrev pageTwoFunctor (f : Hom X Y) (p : ℕ) (q : ℤ) :
    DerivedCategory.Plus (ModuleCat.{w} X) ⥤ AddCommGrpCat.{w} :=
  modulePushforwardDerivedPlus.cohomologyFunctor f q ⋙
    moduleGlobalCohomologyFunctor (X := Y) p

/-- The textbook group `Ext^p(𝒪_Y, H^q(Rf_*K))` on the Leray second page. -/
@[stacks 0732 "Ext presentation of the Leray page two"]
abbrev pageTwo (f : Hom X Y) (K : DerivedCategory.Plus (ModuleCat.{w} X))
    (p : ℕ) (q : ℤ) : AddCommGrpCat.{w} :=
  (pageTwoFunctor (X := X) (Y := Y) f p q).obj K

/-- The map on the `Ext` presentation of the Leray second page. -/
@[stacks 0732 "Ext presentation of Leray page-two naturality"]
abbrev pageTwoMap (f : Hom X Y) {K L : DerivedCategory.Plus (ModuleCat.{w} X)}
    (φ : K ⟶ L) (p : ℕ) (q : ℤ) :
    pageTwo (X := X) (Y := Y) f K p q ⟶ pageTwo (X := X) (Y := Y) f L p q :=
  (pageTwoFunctor (X := X) (Y := Y) f p q).map φ

/-- The canonical Leray second-page functor is naturally isomorphic to its textbook `Ext`
presentation. -/
@[stacks 0732 "Ext comparison for the Leray page-two functor"]
theorem pageTwoFunctor_isIsomorphic (f : Hom X Y) (p : ℕ) (q : ℤ) :
    IsIsomorphic (Leray.pageTwoFunctor (X := X) (Y := Y) f p q)
      (pageTwoFunctor (X := X) (Y := Y) f p q) := sorry

/-- The canonical Leray `(p, q)` target is isomorphic to its textbook `Ext` presentation. -/
@[stacks 0732 "Ext comparison for the Leray page two"]
theorem pageTwo_isIsomorphic (f : Hom X Y)
    (K : DerivedCategory.Plus (ModuleCat.{w} X)) (p : ℕ) (q : ℤ) :
    IsIsomorphic (Leray.pageTwo (X := X) (Y := Y) f K p q)
      (pageTwo (X := X) (Y := Y) f K p q) := sorry

end PageTwo

end Ext

end Leray

end RingedSite.Hom

end
