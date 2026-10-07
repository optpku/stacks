module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology

/-!
# Bivariant classes of morphisms of good algebraic spaces

In Situation 82.2.1, a degree-`p` bivariant class for a morphism `f : X ⟶ Y`
of good algebraic spaces over `B` is a family of additive cap maps
`CH_k(Y') →+ CH_{k - p}(X')` indexed by cartesian squares
`IsPullback i f' f g`, compatible with proper pushforward, flat pullback of
fixed relative dimension, and refined Gysin along a zero scheme and its
pullback. The type of all such classes is `A^p(X ⟶ Y)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Quasi-separation transports along `𝟙 Y ≫ pY = pY`. -/
instance instQuasiSeparated_id_comp {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] : QuasiSeparated (𝟙 Y ≫ pY) :=
  sorry

/-- Local finite type transports along `𝟙 Y ≫ pY = pY`. -/
instance instLocallyOfFiniteType_id_comp {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [LocallyOfFiniteType pY] : LocallyOfFiniteType (𝟙 Y ≫ pY) :=
  sorry

/-- Quasi-separation transports along `g ≫ 𝟙 Y ≫ pY = g ≫ pY`. -/
instance instQuasiSeparated_comp_id {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) (pY : Y ⟶ B) [QuasiSeparated (g ≫ pY)] :
    QuasiSeparated (g ≫ 𝟙 Y ≫ pY) :=
  sorry

/-- Local finite type transports along `g ≫ 𝟙 Y ≫ pY = g ≫ pY`. -/
instance instLocallyOfFiniteType_comp_id {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) (pY : Y ⟶ B) [LocallyOfFiniteType (g ≫ pY)] :
    LocallyOfFiniteType (g ≫ 𝟙 Y ≫ pY) :=
  sorry

namespace BivariantClass

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]

/-- Cartesian-square-indexed additive cap maps
`CH_k(Y') →+ CH_{k - p}(X')` for a degree-`p` bivariant class of `f`. -/
abbrev CapFamily (p : ℤ) :=
  ∀ {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ),
    (g ≫ pY).chowGroup δ k →+ (i ≫ f ≫ pY).chowGroup δ (k - p)

/-- Unfolding of `CapFamily` as cartesian-square-indexed additive maps on
Chow groups. -/
theorem CapFamily_def (p : ℤ) :
    CapFamily δ pY f p =
      ∀ {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
        [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
        (square : IsPullback i f' f g) (k : ℤ),
        (g ≫ pY).chowGroup δ k →+ (i ≫ f ≫ pY).chowGroup δ (k - p) :=
  sorry

/-- Compatibility of cap maps with proper pushforward along a cartesian inner
square. -/
def CompatibleWithProperPushforward {p : ℤ} (cap : CapFamily δ pY f p) : Prop :=
  ∀ {X' Y' X'' Y'' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (outer : IsPullback i f' f g)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    [QuasiSeparated (h ≫ g ≫ pY)] [LocallyOfFiniteType (h ≫ g ≫ pY)]
    [QuasiSeparated ((h ≫ g) ≫ pY)] [LocallyOfFiniteType ((h ≫ g) ≫ pY)]
    [QuasiSeparated (j ≫ i ≫ f ≫ pY)] [LocallyOfFiniteType (j ≫ i ≫ f ≫ pY)]
    [QuasiSeparated ((j ≫ i) ≫ f ≫ pY)] [LocallyOfFiniteType ((j ≫ i) ≫ f ≫ pY)]
    (inner : IsPullback j f'' f' h) [Proper h] [Proper j]
    (k : ℤ) (α : (h ≫ g ≫ pY).chowGroup δ k),
    cap i f' g outer k (Hom.properPushforward δ (h ≫ g ≫ pY) (g ≫ pY) h rfl k α) =
      Hom.properPushforward δ (j ≫ i ≫ f ≫ pY) (i ≫ f ≫ pY) j rfl (k - p)
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) k α)

/-- Compatibility of cap maps with flat pullback of a fixed relative
dimension along a cartesian inner square. -/
def CompatibleWithFlatPullback {p : ℤ} (cap : CapFamily δ pY f p) : Prop :=
  ∀ {X' Y' X'' Y'' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (outer : IsPullback i f' f g)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    [QuasiSeparated (h ≫ g ≫ pY)] [LocallyOfFiniteType (h ≫ g ≫ pY)]
    [QuasiSeparated ((h ≫ g) ≫ pY)] [LocallyOfFiniteType ((h ≫ g) ≫ pY)]
    [QuasiSeparated (j ≫ i ≫ f ≫ pY)] [LocallyOfFiniteType (j ≫ i ≫ f ≫ pY)]
    [QuasiSeparated ((j ≫ i) ≫ f ≫ pY)] [LocallyOfFiniteType ((j ≫ i) ≫ f ≫ pY)]
    (inner : IsPullback j f'' f' h) (r : ℕ) [Flat h] [RelativeDimension h r]
    [Flat j] [RelativeDimension j r]
    (k : ℤ) (α : (g ≫ pY).chowGroup δ k),
    ChowCohomology.castChowGroup δ ((j ≫ i) ≫ f ≫ pY)
        (ChowCohomology.flatPullback_degree_eq k p r)
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k + (r : ℤ))
          (Hom.chowFlatPullback δ (g ≫ pY) (h ≫ g ≫ pY) h r rfl k α)) =
      Hom.chowFlatPullback δ (i ≫ f ≫ pY) ((j ≫ i) ≫ f ≫ pY) j r
        (Category.assoc j i (f ≫ pY)).symm (k - p)
        (cap i f' g outer k α)

/-- Compatibility of cap maps with refined Gysin along a zero scheme
`(L, s)` on `Y'` and a cartesian pullback of that zero scheme to `X'`. -/
def CompatibleWithCartierGysin {p : ℤ} (cap : CapFamily δ pY f p) : Prop :=
  ∀ {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (outer : IsPullback i f' f g)
    (L : Y'.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f').obj L)]
    (f'' : (zeroScheme ((Modules.pullback f').obj L)
        (Modules.sectionsPullback f' L s)).X ⟶ (zeroScheme L s).X)
    (inner : IsPullback
      (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s))
      f'' f' (zeroSchemeι L s))
    [QuasiSeparated (zeroSchemeι L s ≫ g ≫ pY)]
    [LocallyOfFiniteType (zeroSchemeι L s ≫ g ≫ pY)]
    [QuasiSeparated ((zeroSchemeι L s ≫ g) ≫ pY)]
    [LocallyOfFiniteType ((zeroSchemeι L s ≫ g) ≫ pY)]
    [QuasiSeparated
      (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
        i ≫ f ≫ pY)]
    [LocallyOfFiniteType
      (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
        i ≫ f ≫ pY)]
    [QuasiSeparated
      ((zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
          i) ≫ f ≫ pY)]
    [LocallyOfFiniteType
      ((zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
          i) ≫ f ≫ pY)]
    (k : ℤ) (α : (g ≫ pY).chowGroup δ (k + 1)),
    cap (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫ i)
        f'' (zeroSchemeι L s ≫ g) (inner.paste_horiz outer) k
      (Hom.chowGysin δ (g ≫ pY) L s k α) =
      Hom.chowGysin δ (i ≫ f ≫ pY)
        ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) (k - p)
        (ChowCohomology.castChowGroup δ (i ≫ f ≫ pY)
          (ChowCohomology.gysin_degree_eq k p) (cap i f' g outer (k + 1) α))

end BivariantClass

/-- A degree-`p` bivariant class for a morphism `f : X ⟶ Y` of good algebraic
spaces over `B`, i.e. an element of `A^p(X ⟶ Y)`. -/
structure BivariantClass
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]
    (p : ℤ) where
  /-- Cap action `c ∩ - : CH_k(Y') → CH_{k - p}(X')` on a cartesian square. -/
  cap : BivariantClass.CapFamily δ pY f p
  /-- Compatibility with proper pushforward. -/
  map_proper : BivariantClass.CompatibleWithProperPushforward δ pY f cap
  /-- Compatibility with flat pullback of relative dimension `r`. -/
  pullback_flat : BivariantClass.CompatibleWithFlatPullback δ pY f cap
  /-- Compatibility with Gysin pullback along a zero scheme of a section of
  an invertible module. -/
  gysin_cartier : BivariantClass.CompatibleWithCartierGysin δ pY f cap

namespace BivariantClass

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]

/-- Construct a degree-`p` bivariant class from a cap family and the three
bivariant laws. -/
def ofCap {p : ℤ} (cap : CapFamily δ pY f p)
    (map_proper : CompatibleWithProperPushforward δ pY f cap)
    (pullback_flat : CompatibleWithFlatPullback δ pY f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ pY f cap) :
    BivariantClass δ pY f p where
  cap := cap
  map_proper := map_proper
  pullback_flat := pullback_flat
  gysin_cartier := gysin_cartier

/-- `ofCap` recovers the supplied cap family. -/
theorem ofCap_cap {p : ℤ} (cap : CapFamily δ pY f p)
    (map_proper : CompatibleWithProperPushforward δ pY f cap)
    (pullback_flat : CompatibleWithFlatPullback δ pY f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ pY f cap)
    {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    (ofCap δ pY f cap map_proper pullback_flat gysin_cartier).cap i f' g square k =
      cap i f' g square k :=
  sorry

/-- A degree-`p` bivariant class is a cap family compatible with proper
pushforward, flat pullback, and Cartier Gysin. -/
theorem spec {p : ℤ} (c : BivariantClass δ pY f p) :
    CompatibleWithProperPushforward δ pY f c.cap ∧
      CompatibleWithFlatPullback δ pY f c.cap ∧
      CompatibleWithCartierGysin δ pY f c.cap :=
  sorry

/-- Two bivariant classes are equal when their cap maps agree on every
cartesian square. -/
theorem ext {p : ℤ} {c d : BivariantClass δ pY f p}
    (h : ∀ {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
      [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
      [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
      (square : IsPullback i f' f g) (k : ℤ),
      c.cap i f' g square k = d.cap i f' g square k) :
    c = d :=
  sorry

/-- Evaluation of a bivariant class on the chosen fibre product
`X' = Y' ×_Y X`. -/
def cap_pullback {p : ℤ} (c : BivariantClass δ pY f p) {Y' : AlgebraicSpace S}
    (g : Y' ⟶ Y) [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (pullback.fst f g ≫ f ≫ pY)]
    [LocallyOfFiniteType (pullback.fst f g ≫ f ≫ pY)] (k : ℤ) :
    (g ≫ pY).chowGroup δ k →+ (pullback.fst f g ≫ f ≫ pY).chowGroup δ (k - p) :=
  c.cap (pullback.fst f g) (pullback.snd f g) g (IsPullback.of_hasPullback f g) k

/-- `cap_pullback` is the cap map of `c` on the chosen pullback square. -/
theorem cap_pullback_apply {p : ℤ} (c : BivariantClass δ pY f p)
    {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (pullback.fst f g ≫ f ≫ pY)]
    [LocallyOfFiniteType (pullback.fst f g ≫ f ≫ pY)] (k : ℤ) :
    cap_pullback δ pY f c g k =
      c.cap (pullback.fst f g) (pullback.snd f g) g
        (IsPullback.of_hasPullback f g) k :=
  sorry

/-- The pointwise-zero cap family. -/
def zeroCapFamily (p : ℤ) : CapFamily δ pY f p :=
  fun {X' Y'} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
      [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
      [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
      (square : IsPullback i f' f g) (k : ℤ) ↦
    (0 : (g ≫ pY).chowGroup δ k →+ (i ≫ f ≫ pY).chowGroup δ (k - p))

/-- Evaluation of the zero cap family is the zero additive map. -/
theorem zeroCapFamily_apply (p : ℤ) {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    zeroCapFamily δ pY f p i f' g square k = 0 :=
  sorry

/-- The zero cap family satisfies proper-pushforward compatibility. -/
theorem zeroCapFamily_map_proper (p : ℤ) :
    CompatibleWithProperPushforward δ pY f (zeroCapFamily δ pY f p) :=
  sorry

/-- The zero cap family satisfies flat-pullback compatibility. -/
theorem zeroCapFamily_pullback_flat (p : ℤ) :
    CompatibleWithFlatPullback δ pY f (zeroCapFamily δ pY f p) :=
  sorry

/-- The zero cap family satisfies Cartier-Gysin compatibility. -/
theorem zeroCapFamily_gysin_cartier (p : ℤ) :
    CompatibleWithCartierGysin δ pY f (zeroCapFamily δ pY f p) :=
  sorry

/-- The zero bivariant class in degree `p`. -/
def zero (p : ℤ) : BivariantClass δ pY f p :=
  ofCap δ pY f (zeroCapFamily δ pY f p)
    (zeroCapFamily_map_proper δ pY f p)
    (zeroCapFamily_pullback_flat δ pY f p)
    (zeroCapFamily_gysin_cartier δ pY f p)

/-- Evaluation of the zero class is the zero additive map. -/
theorem zero_apply (p : ℤ) {X' Y' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    (zero δ pY f p).cap i f' g square k = 0 :=
  sorry

/-- Reindex a Chow group along an equality of structure morphisms. -/
def chowGroupCongr {X : AlgebraicSpace S} {p p' : X ⟶ B}
    [QuasiSeparated p] [LocallyOfFiniteType p]
    [QuasiSeparated p'] [LocallyOfFiniteType p']
    (hp : p = p') {k : ℤ} :
    p.chowGroup δ k →+ p'.chowGroup δ k :=
  hp ▸ AddMonoidHom.id _

/-- Reindexing along a reflexive equality of structure morphisms is the
identity map. -/
theorem chowGroupCongr_rfl {X : AlgebraicSpace S} (p : X ⟶ B)
    [QuasiSeparated p] [LocallyOfFiniteType p] {k : ℤ} :
    chowGroupCongr δ (rfl : p = p) = AddMonoidHom.id (p.chowGroup δ k) :=
  sorry

/-- Identity-test cap family of a bivariant class of `𝟙 Y`, evaluated on
vertical identity squares. -/
def toIdentityCap {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) :
    ChowCohomology.CapFamily δ pY p :=
  fun {Y'} (g : Y' ⟶ Y)
      [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)] (k : ℤ) ↦
    (chowGroupCongr δ (congrArg (g ≫ ·) (Category.id_comp pY))).comp
      (c.cap g (𝟙 Y') g (IsPullback.id_vert g) k)

/-- `toIdentityCap` evaluates as the identity-square cap, reindexed along
`g ≫ 𝟙 Y ≫ pY = g ≫ pY`. -/
theorem toIdentityCap_apply {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)] (k : ℤ) :
    toIdentityCap δ pY c g k =
      (chowGroupCongr δ (congrArg (g ≫ ·) (Category.id_comp pY))).comp
        (c.cap g (𝟙 Y') g (IsPullback.id_vert g) k) :=
  sorry

/-- The identity-test family of `toIdentity` remains compatible with proper
pushforward. -/
theorem toIdentityCap_map_proper {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) :
    ChowCohomology.CompatibleWithProperPushforward δ pY (toIdentityCap δ pY c) :=
  sorry

/-- The identity-test family of `toIdentity` remains compatible with flat
pullback. -/
theorem toIdentityCap_pullback_flat {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) :
    ChowCohomology.CompatibleWithFlatPullback δ pY (toIdentityCap δ pY c) :=
  sorry

/-- The identity-test family of `toIdentity` remains compatible with Gysin
pullback. -/
theorem toIdentityCap_gysin_cartier {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) :
    ChowCohomology.CompatibleWithCartierGysin δ pY (toIdentityCap δ pY c) :=
  sorry

/-- Recover the identity class of `𝟙 Y` by evaluating on vertical identity
squares. -/
def toIdentity {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) :
    ChowCohomology.degree δ pY p :=
  ChowCohomology.ofCap δ pY (toIdentityCap δ pY c)
    (toIdentityCap_map_proper δ pY c)
    (toIdentityCap_pullback_flat δ pY c)
    (toIdentityCap_gysin_cartier δ pY c)

/-- `toIdentity` evaluates as the cap on the vertical identity square. -/
theorem toIdentity_apply {Y : AlgebraicSpace S} (pY : Y ⟶ B)
    [QuasiSeparated pY] [LocallyOfFiniteType pY] {p : ℤ}
    (c : BivariantClass δ pY (𝟙 Y) p) {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)] (k : ℤ) :
    (toIdentity δ pY c).cap g k =
      (chowGroupCongr δ (congrArg (g ≫ ·) (Category.id_comp pY))).comp
        (c.cap g (𝟙 Y') g (IsPullback.id_vert g) k) :=
  sorry

end BivariantClass

end AlgebraicGeometry.AlgebraicSpace
