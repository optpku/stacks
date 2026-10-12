/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Acyclic

/-!
# Relative Leray spectral sequences for module sheaves

This file owns the ringed-site specialization of the Grothendieck spectral sequence.  The
ordinary realization exposes the classical higher-direct-image targets, while `BoundedBelow`
retains the canonical derived-object formulation.  `Functorial` records one coherent choice of
ordinary realizations and maps, including the identity and composition laws.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

-- Local instance justification (defeq pin): use the standard derived-category model
-- already fixed explicitly by ModuleDerived and moduleLocalization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable {Z : RingedSite.{uZ, vZ, w}}

namespace RelativeLeray

section OrdinaryTargets

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]
variable [HasInjectiveResolutions (ModuleCat.{z} X)]
variable [HasInjectiveResolutions (ModuleCat.{z} Y)]

/-- The `(p, q)` target of the relative Leray spectral sequence. -/
@[stacks 0734 "relative Leray page two"]
abbrev pageTwo (f : Hom X Y) (g : Hom Y Z) (F : ModuleCat.{z} X)
    (p q : ℕ) : ModuleCat.{z} Z :=
  higherDirectImageModule (X := Y) (Y := Z) g
    (higherDirectImageModule (X := X) (Y := Y) f F q) p

/-- The map on relative Leray page-two targets induced by a map of module sheaves. -/
@[stacks 0734 "relative Leray page-two naturality"]
abbrev pageTwoMap (f : Hom X Y) (g : Hom Y Z) {F G : ModuleCat.{z} X}
    (φ : F ⟶ G) (p q : ℕ) :
    pageTwo (X := X) (Y := Y) (Z := Z) f g F p q ⟶
      pageTwo (X := X) (Y := Y) (Z := Z) f g G p q :=
  higherDirectImageModuleMap (X := Y) (Y := Z) g
    (higherDirectImageModuleMap (X := X) (Y := Y) f φ q) p

/-- The degree-`n` abutment target of the relative Leray spectral sequence. -/
@[stacks 0734 "relative Leray abutment"]
abbrev abutment (f : Hom X Y) (g : Hom Y Z) (F : ModuleCat.{z} X)
    (n : ℕ) : ModuleCat.{z} Z :=
  higherDirectImageModule (X := X) (Y := Z) (Hom.comp f g) F n

/-- The map on relative Leray abutment targets induced by a map of module sheaves. -/
@[stacks 0734 "relative Leray abutment naturality"]
abbrev abutmentMap (f : Hom X Y) (g : Hom Y Z) {F G : ModuleCat.{z} X}
    (φ : F ⟶ G) (n : ℕ) :
    abutment (X := X) (Y := Y) (Z := Z) f g F n ⟶
      abutment (X := X) (Y := Y) (Z := Z) f g G n :=
  higherDirectImageModuleMap (X := X) (Y := Z) (Hom.comp f g) φ n

end OrdinaryTargets

end RelativeLeray

section OrdinaryRealization

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]
variable [HasInjectiveResolutions (ModuleCat.{z} X)]
variable [HasInjectiveResolutions (ModuleCat.{z} Y)]

/-- A relative Leray spectral-sequence realization for a module sheaf.  Its second page is
`R^p g_* (R^q f_* F)` and its abutment is `R^n (Hom.comp f g)_* F`. -/
@[stacks 0734 "relative Leray spectral-sequence realization"]
structure RelativeLeray (f : Hom X Y) (g : Hom Y Z) (F : ModuleCat.{z} X)
    extends FilteredComplex.SpectralSequence.Realization (C := ModuleCat.{z} Z) where
  /-- The comparison with the classical relative Leray second page. -/
  pageTwoIso : ∀ p q : ℕ,
    (sequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
      RelativeLeray.pageTwo (X := X) (Y := Y) (Z := Z) f g F p q
  /-- The comparison with the higher direct image along the composite. -/
  abutmentIso : ∀ n : ℕ,
    filtered.underlying.homology (Int.ofNat n) ≅
      RelativeLeray.abutment (X := X) (Y := Y) (Z := Z) f g F n

namespace RelativeLeray

/-- Construct a relative Leray realization from neutral realization data and the two canonical
families of comparison isomorphisms. -/
@[stacks 0734 "constructing a relative Leray realization"]
def ofRealization (f : Hom X Y) (g : Hom Y Z) (F : ModuleCat.{z} X)
    (S : FilteredComplex.SpectralSequence.Realization (C := ModuleCat.{z} Z))
    (pageTwoIso : ∀ p q : ℕ,
      (S.sequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
        pageTwo (X := X) (Y := Y) (Z := Z) f g F p q)
    (abutmentIso : ∀ n : ℕ,
      S.filtered.underlying.homology (Int.ofNat n) ≅
        abutment (X := X) (Y := Y) (Z := Z) f g F n) :
    RelativeLeray (X := X) (Y := Y) (Z := Z) f g F where
  toRealization := S
  pageTwoIso := pageTwoIso
  abutmentIso := abutmentIso

/-- A map of relative Leray realizations over a morphism of module sheaves. -/
@[stacks 0734 "map of relative Leray spectral sequences"]
structure Map {f : Hom X Y} {g : Hom Y Z} {F G : ModuleCat.{z} X}
    (φ : F ⟶ G)
    (S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F)
    (T : RelativeLeray (X := X) (Y := Y) (Z := Z) f g G)
    extends FilteredComplex.SpectralSequence.Realization.Map S.toRealization T.toRealization where
  /-- Naturality of the chosen second-page comparisons. -/
  pageTwoSq : ∀ p q : ℕ,
    CommSq ((sequenceMap.hom 2).f (Int.ofNat p, Int.ofNat q))
      (S.pageTwoIso p q).hom (T.pageTwoIso p q).hom
      (pageTwoMap (X := X) (Y := Y) (Z := Z) f g φ p q)
  /-- Naturality of the chosen abutment comparisons. -/
  abutmentSq : ∀ n : ℕ,
    CommSq (HomologicalComplex.homologyMap (S.filtered.underlyingMap filteredMap) (Int.ofNat n))
      (S.abutmentIso n).hom (T.abutmentIso n).hom
      (abutmentMap (X := X) (Y := Y) (Z := Z) f g φ n)

namespace Map

/-- Two relative Leray maps agree when their filtered and spectral-sequence maps agree. -/
@[ext, stacks 0734 "extensionality of relative Leray maps"]
theorem ext {f : Hom X Y} {g : Hom Y Z} {F G : ModuleCat.{z} X} {φ : F ⟶ G}
    {S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F}
    {T : RelativeLeray (X := X) (Y := Y) (Z := Z) f g G}
    {m n : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) φ S T}
    (hFiltered : m.filteredMap = n.filteredMap)
    (hSequence : m.sequenceMap = n.sequenceMap) : m = n := sorry

/-- Identity maps commute with the relative Leray second-page comparisons. -/
theorem idPageTwo {f : Hom X Y} {g : Hom Y Z} {F : ModuleCat.{z} X}
    (S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F) : ∀ p q : ℕ,
    CommSq (((𝟙 S.sequence : S.sequence ⟶ S.sequence).hom 2).f
        (Int.ofNat p, Int.ofNat q))
      (S.pageTwoIso p q).hom (S.pageTwoIso p q).hom
      (pageTwoMap (X := X) (Y := Y) (Z := Z) f g (𝟙 F) p q) := sorry

/-- Identity maps commute with the relative Leray abutment comparisons. -/
theorem idAbutment {f : Hom X Y} {g : Hom Y Z} {F : ModuleCat.{z} X}
    (S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F) : ∀ n : ℕ,
    CommSq (HomologicalComplex.homologyMap
        (S.filtered.underlyingMap (𝟙 S.filtered)) (Int.ofNat n))
      (S.abutmentIso n).hom (S.abutmentIso n).hom
      (abutmentMap (X := X) (Y := Y) (Z := Z) f g (𝟙 F) n) := sorry

/-- The identity map of a relative Leray realization. -/
@[stacks 0734 "identity map of a relative Leray spectral sequence"]
noncomputable def id {f : Hom X Y} {g : Hom Y Z} {F : ModuleCat.{z} X}
    (S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F) :
    RelativeLeray.Map (X := X) (Y := Y) (Z := Z) (𝟙 F) S S where
  toMap := FilteredComplex.SpectralSequence.Realization.Map.id S.toRealization
  pageTwoSq := idPageTwo S
  abutmentSq := idAbutment S

/-- Composite maps commute with the relative Leray second-page comparisons. -/
theorem compPageTwo {f : Hom X Y} {g : Hom Y Z} {F G H : ModuleCat.{z} X}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    {S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F}
    {T : RelativeLeray (X := X) (Y := Y) (Z := Z) f g G}
    {U : RelativeLeray (X := X) (Y := Y) (Z := Z) f g H}
    (m : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) φ S T)
    (n : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) ψ T U) : ∀ p q : ℕ,
    CommSq (((m.sequenceMap ≫ n.sequenceMap).hom 2).f (Int.ofNat p, Int.ofNat q))
      (S.pageTwoIso p q).hom (U.pageTwoIso p q).hom
      (pageTwoMap (X := X) (Y := Y) (Z := Z) f g (φ ≫ ψ) p q) := sorry

/-- Composite maps commute with the relative Leray abutment comparisons. -/
theorem compAbutment {f : Hom X Y} {g : Hom Y Z} {F G H : ModuleCat.{z} X}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    {S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F}
    {T : RelativeLeray (X := X) (Y := Y) (Z := Z) f g G}
    {U : RelativeLeray (X := X) (Y := Y) (Z := Z) f g H}
    (m : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) φ S T)
    (n : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) ψ T U) : ∀ k : ℕ,
    CommSq (HomologicalComplex.homologyMap
        (S.filtered.underlyingMap (m.filteredMap ≫ n.filteredMap)) (Int.ofNat k))
      (S.abutmentIso k).hom (U.abutmentIso k).hom
      (abutmentMap (X := X) (Y := Y) (Z := Z) f g (φ ≫ ψ) k) := sorry

/-- Composition of maps of relative Leray realizations. -/
@[stacks 0734 "composition of maps of relative Leray spectral sequences"]
noncomputable def comp {f : Hom X Y} {g : Hom Y Z} {F G H : ModuleCat.{z} X}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    {S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F}
    {T : RelativeLeray (X := X) (Y := Y) (Z := Z) f g G}
    {U : RelativeLeray (X := X) (Y := Y) (Z := Z) f g H}
    (m : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) φ S T)
    (n : RelativeLeray.Map (X := X) (Y := Y) (Z := Z) ψ T U) :
    RelativeLeray.Map (X := X) (Y := Y) (Z := Z) (φ ≫ ψ) S U where
  toMap := FilteredComplex.SpectralSequence.Realization.Map.comp m.toMap n.toMap
  pageTwoSq := compPageTwo m n
  abutmentSq := compAbutment m n

end Map

/-- A coherent relative Leray spectral sequence, functorial in the input module sheaf. -/
@[stacks 0734 "functorial relative Leray spectral sequence"]
structure Functorial (f : Hom X Y) (g : Hom Y Z) where
  /-- The chosen relative Leray realization at each module sheaf. -/
  obj : (F : ModuleCat.{z} X) →
    RelativeLeray (X := X) (Y := Y) (Z := Z) f g F
  /-- The chosen map of realizations over each morphism of module sheaves. -/
  map : ∀ {F G : ModuleCat.{z} X} (φ : F ⟶ G),
    RelativeLeray.Map (X := X) (Y := Y) (Z := Z) φ (obj F) (obj G)
  /-- The chosen realization maps preserve identities. -/
  map_id : ∀ F : ModuleCat.{z} X,
    map (𝟙 F) = RelativeLeray.Map.id (X := X) (Y := Y) (Z := Z) (obj F)
  /-- The chosen realization maps preserve composition. -/
  map_comp : ∀ {F G H : ModuleCat.{z} X} (φ : F ⟶ G) (ψ : G ⟶ H),
    map (φ ≫ ψ) = RelativeLeray.Map.comp (X := X) (Y := Y) (Z := Z)
      (map φ) (map ψ)

end RelativeLeray

end OrdinaryRealization

namespace RelativeLeray

section Acyclicity

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf Y.siteTopology AddCommGrpCat.{z})]

/-- The acyclicity input for the Grothendieck construction: the first pushforward of an
injective module sheaf is right-acyclic for the second pushforward. -/
@[stacks 0734 "relative Leray acyclicity input"]
theorem isAcyclic (f : Hom X Y) (g : Hom Y Z)
    (I : ModuleCat.{z} X) [Injective I] :
    Functor.RightAcyclic.Bounded g.modulePushforward
      (f.modulePushforward.obj I) := sorry

end Acyclicity

section OrdinaryExistence

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]
variable [IsGrothendieckAbelian.{z} (ModuleCat.{z} X)]
variable [IsGrothendieckAbelian.{z} (ModuleCat.{z} Y)]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf Y.siteTopology AddCommGrpCat.{z})]

/-- Stacks 0734: relative Leray spectral sequences can be chosen functorially in the module
sheaf, with the classical higher-direct-image second page and abutment. -/
@[stacks 0734]
theorem functorial (f : Hom X Y) (g : Hom Y Z) :
    Nonempty (Functorial (X := X) (Y := Y) (Z := Z) f g) := sorry

/-- A relative Leray spectral-sequence realization exists for every module sheaf. -/
@[stacks 0734 "existence of a relative Leray spectral sequence"]
theorem nonempty (f : Hom X Y) (g : Hom Y Z) (F : ModuleCat.{z} X) :
    Nonempty (RelativeLeray (X := X) (Y := Y) (Z := Z) f g F) := sorry

/-- A morphism of module sheaves admits compatible relative Leray realizations and a map between
them.  For a coherent choice, use `RelativeLeray.Functorial.map`. -/
@[stacks 0734 "relative Leray map existence"]
theorem existsMap (f : Hom X Y) (g : Hom Y Z) {F G : ModuleCat.{z} X} (φ : F ⟶ G) :
    ∃ (S : RelativeLeray (X := X) (Y := Y) (Z := Z) f g F)
      (T : RelativeLeray (X := X) (Y := Y) (Z := Z) f g G),
      Nonempty (RelativeLeray.Map (X := X) (Y := Y) (Z := Z) φ S T) := sorry

end OrdinaryExistence

section BoundedBelow

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]
variable [HasInjectiveResolutions (ModuleCat.{z} Y)]

/-- The relative Leray realization for a bounded-below derived module object. -/
@[stacks 0734 "bounded-below relative Leray spectral sequence"]
abbrev BoundedBelow (f : Hom X Y) (g : Hom Y Z)
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((Hom.comp f g).modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) :=
  Functor.RightDerived.Grothendieck.SpectralSequence g.modulePushforward
    (modulePushforwardDerivedPlus f) (modulePushforwardDerivedPlus (Hom.comp f g)) K

namespace BoundedBelow

/-- The `(p, q)` target of the bounded-below relative Leray spectral sequence. -/
@[stacks 0734 "bounded-below relative Leray page two"]
abbrev pageTwo (f : Hom X Y) (g : Hom Y Z)
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) (p : ℕ) (q : ℤ) : ModuleCat.{z} Z :=
  higherDirectImageModule (X := Y) (Y := Z) g
    (modulePushforwardDerivedPlus.cohomology f K q) p

/-- The degree-`n` abutment of the bounded-below relative Leray spectral sequence. -/
@[stacks 0734 "bounded-below relative Leray abutment"]
abbrev abutment (f : Hom X Y) (g : Hom Y Z)
    [Functor.HasRightDerivedFunctor
      ((Hom.comp f g).modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) (n : ℤ) : ModuleCat.{z} Z :=
  modulePushforwardDerivedPlus.cohomology (Hom.comp f g) K n

/-- A map of bounded-below relative Leray realizations over a derived-object morphism. -/
abbrev Map {f : Hom X Y} {g : Hom Y Z}
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((Hom.comp f g).modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    {K L : DerivedCategory.Plus (ModuleCat.{z} X)} (φ : K ⟶ L)
    (S : BoundedBelow (X := X) (Y := Y) (Z := Z) f g K)
    (T : BoundedBelow (X := X) (Y := Y) (Z := Z) f g L) :=
  Functor.RightDerived.Grothendieck.SpectralSequence.Map φ S T

namespace Map

export Functor.RightDerived.Grothendieck.SpectralSequence.Map
  (ext ext_filteredMap pageTwo_hom abutment_hom id comp reindex reindex_rfl
    id_comp comp_id assoc)

end Map

/-- The generic functorial Grothendieck owner specialized to bounded-below relative Leray
realizations. -/
@[stacks 0734 "functorial bounded-below relative Leray spectral sequence"]
abbrev Functorial (f : Hom X Y) (g : Hom Y Z)
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((Hom.comp f g).modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :=
  Functor.RightDerived.Grothendieck.SpectralSequence.Functorial
    g.modulePushforward (modulePushforwardDerivedPlus f)
    (modulePushforwardDerivedPlus (Hom.comp f g))

end BoundedBelow

end BoundedBelow

section BoundedBelowExistence

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{max uZ vZ, z}]
variable [IsGrothendieckAbelian.{z} (ModuleCat.{z} X)]
variable [IsGrothendieckAbelian.{z} (ModuleCat.{z} Y)]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf Y.siteTopology AddCommGrpCat.{z})]

/-- Bounded-below relative Leray realizations can be chosen coherently and functorially in the
derived module. -/
@[stacks 0734 "functorial bounded-below relative Leray existence"]
theorem BoundedBelow.functorial (f : Hom X Y) (g : Hom Y Z) :
    Nonempty (BoundedBelow.Functorial (X := X) (Y := Y) (Z := Z) f g) := sorry

/-- The bounded-below relative Leray realization exists for every derived module object. -/
@[stacks 0734 "bounded-below relative Leray existence"]
theorem BoundedBelow.nonempty (f : Hom X Y) (g : Hom Y Z)
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) :
    Nonempty (BoundedBelow (X := X) (Y := Y) (Z := Z) f g K) := sorry

/-- A bounded-below derived-object morphism admits compatible relative Leray realizations and a
map between them. -/
@[stacks 0734 "bounded-below relative Leray map existence"]
theorem BoundedBelow.existsMap (f : Hom X Y) (g : Hom Y Z)
    {K L : DerivedCategory.Plus (ModuleCat.{z} X)} (φ : K ⟶ L) :
    ∃ (S : BoundedBelow (X := X) (Y := Y) (Z := Z) f g K)
      (T : BoundedBelow (X := X) (Y := Y) (Z := Z) f g L),
      Nonempty (BoundedBelow.Map (X := X) (Y := Y) (Z := Z) φ S T) := sorry

end BoundedBelowExistence

end RelativeLeray

end RingedSite.Hom
