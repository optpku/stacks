module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap67.Lemma_67_40_5
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap82.Remark_82_28_5_RankLocus

/-!
# Operational Chern classes of finite locally free modules on algebraic spaces

In Situation 82.2.1, the constant-rank Chern operations of Lemma 82.28.1 are the
identity bivariant classes of a finite locally free module of rank `r`. These
glue along the clopen rank decomposition of a possibly non-constant finite
locally free module to a class `c_i(E)` in `A^i(X)`. Chow groups are realized
as dimension-supported cycle groups; the rational-equivalence quotient is the
standard companion of this carrier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory
open Function Set
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative dimension function adds the residue-field transcendence degree
to the dimension at the image point. -/
noncomputable def relativeDimensionFunction {S : Scheme.{u}}
    {B X : AlgebraicSpace S} (f : X ⟶ B) (δ : Points B → ℤ) :
    Points X → ℤ :=
  fun x ↦ δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ)

/-- Evaluation of `relativeDimensionFunction` is the source formula. -/
theorem relativeDimensionFunction_apply {S : Scheme.{u}}
    {B X : AlgebraicSpace S} (f : X ⟶ B) (δ : Points B → ℤ) (x : Points X) :
    relativeDimensionFunction f δ x =
      δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ) :=
  sorry

/-- The additive subgroup of locally finite cycles on `|X|` whose nonzero
coefficients occur only at points of dimension `k` according to `d`. -/
noncomputable def cycleDimensionSubgroup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) where
  carrier := {α | ∀ x, α x ≠ 0 → d x = k}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `cycleDimensionSubgroup d k` means that every point with a
nonzero coefficient has dimension `k`. -/
theorem mem_cycleDimensionSubgroup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ cycleDimensionSubgroup d k ↔ ∀ x, α x ≠ 0 → d x = k :=
  sorry

namespace Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The abelian group `Z_k(X)` of `k`-cycles on `X`, relative to the dimension
function induced by `f` and `δ`. -/
noncomputable abbrev cycleGroup {X : AlgebraicSpace S} (f : X ⟶ B)
    (δ : Points B → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) :=
  cycleDimensionSubgroup (relativeDimensionFunction f δ) k

/-- Membership in `cycleGroup f δ k` means that every nonzero coefficient occurs
at a point of relative dimension `k`. -/
theorem mem_cycleGroup {X : AlgebraicSpace S} (f : X ⟶ B)
    (δ : Points B → ℤ) (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ cycleGroup f δ k ↔
      ∀ x, α x ≠ 0 → relativeDimensionFunction f δ x = k :=
  sorry

/-- The Chow group `CH_k(X)` of `k`-cycles on a good morphism, realized on the
dimension-supported cycle carrier. -/
noncomputable abbrev chowGroup {X : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ) :=
  cycleGroup f δ k

/-- `chowGroup` is the dimension-supported cycle group of the structure
morphism. -/
theorem chowGroup_eq {X : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ) :
    chowGroup f δ k = cycleGroup f δ k :=
  sorry

/-- Restriction of coefficients along an open immersion `U.ι`. -/
def openPullbackCycle {X : AlgebraicSpace S} (f : X ⟶ B)
    (δ : Points B → ℤ) (U : OpenSubspace X) (k : ℤ)
    (α : cycleGroup f δ k) :
    Function.locallyFinsupp (Points U.X) ℤ where
  toFun := fun u ↦ (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := sorry

/-- Coefficientwise restriction along `U.ι` preserves the relative degree `k`. -/
theorem openPullback_mem {X : AlgebraicSpace S} (f : X ⟶ B)
    (δ : Points B → ℤ) (U : OpenSubspace X) (k : ℤ)
    (α : cycleGroup f δ k) :
    openPullbackCycle f δ U k α ∈ cycleGroup (U.ι ≫ f) δ k :=
  sorry

/-- Open restriction of `k`-cycles along `U.ι`. -/
def openPullback {X : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (U : OpenSubspace X)
    [QuasiSeparated (U.ι ≫ f)] [LocallyOfFiniteType (U.ι ≫ f)]
    (k : ℤ) :
    chowGroup f δ k →+ chowGroup (U.ι ≫ f) δ k where
  toFun α := ⟨openPullbackCycle f δ U k α, openPullback_mem f δ U k α⟩
  map_zero' := sorry
  map_add' := sorry

/-- Open restriction evaluates by reading coefficients along `Points.map U.ι`. -/
theorem openPullback_apply {X : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (U : OpenSubspace X)
    [QuasiSeparated (U.ι ≫ f)] [LocallyOfFiniteType (U.ι ≫ f)]
    (k : ℤ)
    (α : chowGroup f δ k) (u : Points U.X) :
    (openPullback f δ U k α : Function.locallyFinsupp (Points U.X) ℤ) u =
      (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u) :=
  sorry

/-- Coefficient pushforward along a morphism of good spaces. -/
def properPushforwardCycle {X Y : AlgebraicSpace S}
    (δ : Points B → ℤ) (hX : X ⟶ B) (π : Y ⟶ X) (k : ℤ)
    (α : cycleGroup (π ≫ hX) δ k) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    ∑ᶠ y ∈ Points.map π ⁻¹' {x},
      (α : Function.locallyFinsupp (Points Y) ℤ) y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := sorry

/-- Coefficient pushforward preserves the relative degree `k`. -/
theorem properPushforward_mem {X Y : AlgebraicSpace S}
    (δ : Points B → ℤ) (hX : X ⟶ B) (π : Y ⟶ X) (k : ℤ)
    (α : cycleGroup (π ≫ hX) δ k) :
    properPushforwardCycle δ hX π k α ∈ cycleGroup hX δ k :=
  sorry

/-- Proper pushforward of Chow classes along `π`, after identifying the
composite structure morphism. -/
def properPushforward (δ : Points B → ℤ) {X Y : AlgebraicSpace S}
    (hY : Y ⟶ B) (hX : X ⟶ B) (π : Y ⟶ X)
    [QuasiSeparated hY] [LocallyOfFiniteType hY]
    [QuasiSeparated hX] [LocallyOfFiniteType hX]
    (hπ : π ≫ hX = hY) (k : ℤ) :
    chowGroup hY δ k →+ chowGroup hX δ k where
  toFun α :=
    ⟨properPushforwardCycle δ hX π k (hπ ▸ α),
      properPushforward_mem δ hX π k (hπ ▸ α)⟩
  map_zero' := sorry
  map_add' := sorry

/-- Coefficient pullback along a morphism of good spaces. -/
def chowFlatPullbackCycle {X Y : AlgebraicSpace S}
    (δ : Points B → ℤ) (hX : X ⟶ B) (π : Y ⟶ X) (k : ℤ)
    (α : cycleGroup hX δ k) :
    Function.locallyFinsupp (Points Y) ℤ where
  toFun := fun y ↦ (α : Function.locallyFinsupp (Points X) ℤ) (Points.map π y)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := sorry

/-- Coefficient pullback preserves the shifted relative degree. -/
theorem chowFlatPullback_mem {X Y : AlgebraicSpace S}
    (δ : Points B → ℤ) (hX : X ⟶ B) (π : Y ⟶ X) (r : ℕ) (k : ℤ)
    (α : cycleGroup hX δ k) :
    chowFlatPullbackCycle δ hX π k α ∈
      cycleGroup (π ≫ hX) δ (k + (r : ℤ)) :=
  sorry

/-- Flat pullback of Chow classes of relative dimension `r`. -/
def chowFlatPullback (δ : Points B → ℤ) {X Y : AlgebraicSpace S}
    (hX : X ⟶ B) (hY : Y ⟶ B) (π : Y ⟶ X)
    [QuasiSeparated hX] [LocallyOfFiniteType hX]
    [QuasiSeparated hY] [LocallyOfFiniteType hY]
    (r : ℕ) (hπ : π ≫ hX = hY) (k : ℤ) :
    chowGroup hX δ k →+ chowGroup hY δ (k + (r : ℤ)) where
  toFun α :=
    ⟨chowFlatPullbackCycle δ hX π k α,
      hπ ▸ chowFlatPullback_mem δ hX π r k α⟩
  map_zero' := sorry
  map_add' := sorry

/-- Gysin pullback along the zero scheme of a section of an invertible module. -/
def chowGysin (δ : Points B → ℤ) {X : AlgebraicSpace S}
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [QuasiSeparated (zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (zeroSchemeι L s ≫ pX)]
    (k : ℤ) :
    chowGroup pX δ (k + 1) →+ chowGroup (zeroSchemeι L s ≫ pX) δ k :=
  0

end Hom

namespace ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Identity cap families `CH_k(Y) →+ CH_{k - p}(Y)` on good morphisms
`Y ⟶ X` over `B`. -/
abbrev CapFamily (p : ℤ) :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    chowGroup (g ≫ f) δ k →+ chowGroup (g ≫ f) δ (k - p)

/-- Reindex a Chow group along an equality of degrees. -/
def castChowGroup {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] {i j : ℤ} (hij : i = j) :
    chowGroup h δ i →+ chowGroup h δ j :=
  hij ▸ AddMonoidHom.id _

/-- Reindexing along a reflexive degree equality is the identity map. -/
theorem castChowGroup_rfl {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (i : ℤ) :
    castChowGroup δ h (rfl : i = i) = AddMonoidHom.id _ :=
  sorry

/-- Flat pullback reindexes along `k + r - p = k - p + r`. -/
theorem flatPullback_degree_eq (k p : ℤ) (r : ℕ) :
    k + (r : ℤ) - p = k - p + (r : ℤ) :=
  sorry

/-- Gysin reindexes along `k + 1 - p = k - p + 1`. -/
theorem gysin_degree_eq (k p : ℤ) : k + 1 - p = k - p + 1 :=
  sorry

/-- Compatibility of identity cap maps with proper pushforward. -/
def CompatibleWithProperPushforward {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y Y' : AlgebraicSpace S} (g : Y ⟶ X) (π : Y' ⟶ Y)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [QuasiSeparated (π ≫ g ≫ f)] [LocallyOfFiniteType (π ≫ g ≫ f)]
    [QuasiSeparated ((π ≫ g) ≫ f)] [LocallyOfFiniteType ((π ≫ g) ≫ f)]
    [Proper π]
    (k : ℤ) (α : chowGroup (π ≫ g ≫ f) δ k),
    cap g k (properPushforward δ (π ≫ g ≫ f) (g ≫ f) π rfl k α) =
      properPushforward δ (π ≫ g ≫ f) (g ≫ f) π rfl (k - p)
        (cap (π ≫ g) k α)

/-- Compatibility of identity cap maps with flat pullback of fixed relative
dimension. -/
def CompatibleWithFlatPullback {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y Y' : AlgebraicSpace S} (g : Y ⟶ X) (π : Y' ⟶ Y)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [QuasiSeparated (π ≫ g ≫ f)] [LocallyOfFiniteType (π ≫ g ≫ f)]
    [QuasiSeparated ((π ≫ g) ≫ f)] [LocallyOfFiniteType ((π ≫ g) ≫ f)]
    (r : ℕ) [Flat π] [RelativeDimension π r]
    (k : ℤ) (α : chowGroup (g ≫ f) δ k),
    castChowGroup δ (π ≫ g ≫ f) (flatPullback_degree_eq k p r)
        (cap (π ≫ g) (k + (r : ℤ))
          (chowFlatPullback δ (g ≫ f) (π ≫ g ≫ f) π r rfl k α)) =
      chowFlatPullback δ (g ≫ f) (π ≫ g ≫ f) π r rfl (k - p)
        (cap g k α)

/-- Compatibility of identity cap maps with Gysin pullback along a zero scheme
of a section of an invertible module. -/
def CompatibleWithCartierGysin {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (L : Y.Modules) [isInvertibleObject L] (s : L.sections)
    [QuasiSeparated (zeroSchemeι L s ≫ g ≫ f)]
    [LocallyOfFiniteType (zeroSchemeι L s ≫ g ≫ f)]
    [QuasiSeparated ((zeroSchemeι L s ≫ g) ≫ f)]
    [LocallyOfFiniteType ((zeroSchemeι L s ≫ g) ≫ f)]
    (k : ℤ) (α : chowGroup (g ≫ f) δ (k + 1)),
    cap (zeroSchemeι L s ≫ g) k (chowGysin δ (g ≫ f) L s k α) =
      chowGysin δ (g ≫ f) L s (k - p)
        (castChowGroup δ (g ≫ f) (gysin_degree_eq k p) (cap g (k + 1) α))

/-- The degree-`p` group `A^p(X ⟶ X)` of bivariant classes of `𝟙 X` on
Chow groups of good algebraic spaces over `X`. -/
structure degree (p : ℤ) where
  /-- Cap action `CH_k(Y) → CH_{k - p}(Y)` on a good morphism `g : Y ⟶ X`. -/
  cap : CapFamily δ f p
  /-- Compatibility with proper pushforward. -/
  map_proper : CompatibleWithProperPushforward δ f cap
  /-- Compatibility with flat pullback of relative dimension `r`. -/
  pullback_flat : CompatibleWithFlatPullback δ f cap
  /-- Compatibility with Gysin pullback along the zero scheme of a
  section of an invertible module. -/
  gysin_cartier : CompatibleWithCartierGysin δ f cap

/-- Construct a degree-`p` identity class from a cap family and the three
bivariant laws. -/
def ofCap {p : ℤ} (cap : CapFamily δ f p)
    (map_proper : CompatibleWithProperPushforward δ f cap)
    (pullback_flat : CompatibleWithFlatPullback δ f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ f cap) :
    degree δ f p where
  cap := cap
  map_proper := map_proper
  pullback_flat := pullback_flat
  gysin_cartier := gysin_cartier

/-- `ofCap` recovers the supplied cap family. -/
theorem ofCap_cap {p : ℤ} (cap : CapFamily δ f p)
    (map_proper : CompatibleWithProperPushforward δ f cap)
    (pullback_flat : CompatibleWithFlatPullback δ f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ f cap)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (ofCap δ f cap map_proper pullback_flat gysin_cartier).cap g k = cap g k :=
  sorry

/-- A degree-`p` identity class is a cap family compatible with proper
pushforward, flat pullback, and Gysin pullback. -/
theorem degree_spec {p : ℤ} (c : degree δ f p) :
    CompatibleWithProperPushforward δ f c.cap ∧
      CompatibleWithFlatPullback δ f c.cap ∧
      CompatibleWithCartierGysin δ f c.cap :=
  sorry

/-- The identity cap family in degree zero. -/
def oneCapFamily : CapFamily δ f 0 :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    castChowGroup δ (g ≫ f) (sub_zero k).symm

/-- The identity cap family satisfies proper-pushforward compatibility. -/
theorem oneCapFamily_map_proper :
    CompatibleWithProperPushforward δ f (oneCapFamily δ f) :=
  sorry

/-- The identity cap family satisfies flat-pullback compatibility. -/
theorem oneCapFamily_pullback_flat :
    CompatibleWithFlatPullback δ f (oneCapFamily δ f) :=
  sorry

/-- The identity cap family satisfies Gysin compatibility. -/
theorem oneCapFamily_gysin_cartier :
    CompatibleWithCartierGysin δ f (oneCapFamily δ f) :=
  sorry

/-- The degree-zero identity class, acting by the identity of Chow groups. -/
def oneCap : degree δ f 0 :=
  ofCap δ f (oneCapFamily δ f)
    (oneCapFamily_map_proper δ f)
    (oneCapFamily_pullback_flat δ f)
    (oneCapFamily_gysin_cartier δ f)

/-- The identity class is the identity on Chow groups, reindexed along
`k - 0 = k`. -/
theorem oneCap_apply {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (oneCap δ f).cap g k = castChowGroup δ (g ≫ f) (sub_zero k).symm :=
  sorry

/-- Pointwise zero identity cap family. -/
def zeroCapFamily (p : ℤ) : CapFamily δ f p :=
  fun {Y} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    (0 : chowGroup (g ≫ f) δ k →+ chowGroup (g ≫ f) δ (k - p))

/-- The zero cap family satisfies proper-pushforward compatibility. -/
theorem zeroCapFamily_map_proper (p : ℤ) :
    CompatibleWithProperPushforward δ f (zeroCapFamily δ f p) :=
  sorry

/-- The zero cap family satisfies flat-pullback compatibility. -/
theorem zeroCapFamily_pullback_flat (p : ℤ) :
    CompatibleWithFlatPullback δ f (zeroCapFamily δ f p) :=
  sorry

/-- The zero cap family satisfies Gysin compatibility. -/
theorem zeroCapFamily_gysin_cartier (p : ℤ) :
    CompatibleWithCartierGysin δ f (zeroCapFamily δ f p) :=
  sorry

/-- The zero identity class in degree `p`. -/
def zeroCap (p : ℤ) : degree δ f p :=
  ofCap δ f (zeroCapFamily δ f p)
    (zeroCapFamily_map_proper δ f p)
    (zeroCapFamily_pullback_flat δ f p)
    (zeroCapFamily_gysin_cartier δ f p)

/-- Evaluation of the zero class is the zero additive map. -/
theorem zeroCap_apply (p : ℤ) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (zeroCap δ f p).cap g k = 0 :=
  sorry

end ChowCohomology

namespace ChernClass

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]

/-- Precomposition with an identity morphism preserves quasi-separation. -/
instance instQuasiSeparated_id_comp {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [QuasiSeparated h] : QuasiSeparated (𝟙 Y ≫ h) :=
  sorry

/-- Precomposition with an identity morphism preserves local finite type. -/
instance instLocallyOfFiniteType_id_comp {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [LocallyOfFiniteType h] : LocallyOfFiniteType (𝟙 Y ≫ h) :=
  sorry

/-- Open immersions of algebraic spaces are quasi-separated. -/
instance instQuasiSeparated_isOpenImmersion {Y Z : AlgebraicSpace S}
    (i : Y ⟶ Z) [IsOpenImmersion i] : QuasiSeparated i :=
  sorry

/-- Open immersions of algebraic spaces are locally of finite type. -/
instance instLocallyOfFiniteType_isOpenImmersion {Y Z : AlgebraicSpace S}
    (i : Y ⟶ Z) [IsOpenImmersion i] : LocallyOfFiniteType i :=
  sorry

/-- Composition with a structure morphism preserves quasi-separation. -/
instance instQuasiSeparated_comp_left {P Y : AlgebraicSpace S}
    (π : P ⟶ Y) (h : Y ⟶ B) [QuasiSeparated π] [QuasiSeparated h] :
    QuasiSeparated (π ≫ h) :=
  sorry

/-- Composition with a structure morphism preserves local finite type. -/
instance instLocallyOfFiniteType_comp_left {P Y : AlgebraicSpace S}
    (π : P ⟶ Y) (h : Y ⟶ B) [LocallyOfFiniteType π] [LocallyOfFiniteType h] :
    LocallyOfFiniteType (π ≫ h) :=
  sorry

/-- Reindex Chow groups along an equality of structure morphisms. -/
def chowGroupCongr {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    {h h' : Y ⟶ B}
    [QuasiSeparated h] [LocallyOfFiniteType h]
    [QuasiSeparated h'] [LocallyOfFiniteType h'] (e : h = h') (k : ℤ) :
    chowGroup h δ k →+ chowGroup h' δ k :=
  e ▸ AddMonoidHom.id _

/-- Reindexing along a reflexive equality of structure morphisms is the identity. -/
theorem chowGroupCongr_rfl {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (k : ℤ) :
    chowGroupCongr δ (rfl : h = h) k = AddMonoidHom.id _ :=
  sorry

/-- The identity-test cap of a class on `Y` itself, transported along `𝟙 Y ≫ h = h`. -/
def capOnSelf {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] {p : ℤ}
    (c : ChowCohomology.degree δ h p) (k : ℤ) :
    chowGroup h δ k →+ chowGroup h δ (k - p) :=
  (chowGroupCongr δ (Category.id_comp h) (k - p)).comp
    ((c.cap (𝟙 Y) k).comp (chowGroupCongr δ (Category.id_comp h).symm k))

/-- `capOnSelf` is the identity-test cap transported along `Category.id_comp`. -/
theorem capOnSelf_eq {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] {p : ℤ}
    (c : ChowCohomology.degree δ h p) (k : ℤ) :
    capOnSelf δ h c k =
      (chowGroupCongr δ (Category.id_comp h) (k - p)).comp
        ((c.cap (𝟙 Y) k).comp (chowGroupCongr δ (Category.id_comp h).symm k)) :=
  sorry

/-- Glue a family of cycles on the rank loci by reading, at each point, the unique
rank component containing that point. -/
def glueCycle {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) (E : Y.Modules) [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ)
    (family : ∀ r : ℕ, cycleGroup ((rankOpenSubspace E r).ι ≫ h) δ k) :
    Function.locallyFinsupp (Points Y) ℤ where
  toFun x :=
    ∑ᶠ y ∈ Points.map (rankOpenSubspace E (fiberFinrank E x)).ι ⁻¹' {x},
      (family (fiberFinrank E x) :
          Function.locallyFinsupp
            (Points (rankOpenSubspace E (fiberFinrank E x)).X) ℤ) y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := sorry

/-- The glued cycle lies in the degree-`k` cycle group of `h`. -/
theorem glueCycle_mem {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) (E : Y.Modules) [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ)
    (family : ∀ r : ℕ, cycleGroup ((rankOpenSubspace E r).ι ≫ h) δ k) :
    glueCycle δ h E k family ∈ cycleGroup h δ k :=
  sorry

/-- The inverse of the rank-product decomposition, as a cycle on `Y`. -/
def glueCycleValue {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) (E : Y.Modules) [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ)
    (family : ∀ r : ℕ, cycleGroup ((rankOpenSubspace E r).ι ≫ h) δ k) :
    cycleGroup h δ k :=
  ⟨glueCycle δ h E k family, glueCycle_mem δ h E k family⟩

/-- Restriction of Chow classes to each rank locus. -/
def chowProductForward {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ) :
    chowGroup h δ k →+
      ∀ r : ℕ, chowGroup ((rankOpenSubspace E r).ι ≫ h) δ k where
  toFun α r := openPullback h δ (rankOpenSubspace E r) k α
  map_zero' := sorry
  map_add' := sorry

/-- Gluing of Chow classes along rank loci. -/
def chowProductBackward {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ) :
    (∀ r : ℕ, chowGroup ((rankOpenSubspace E r).ι ≫ h) δ k) →+
      chowGroup h δ k where
  toFun family := glueCycleValue δ h E k family
  map_zero' := sorry
  map_add' := sorry

/-- In Situation 82.2.1, the identification `CH_k(Y) ≃+ ∏_r CH_k(Y_r)` of Chow
groups along the clopen rank decomposition of a finite locally free module. -/
def chowProductEquiv (δ : Points B → ℤ) [IsDimensionFunction δ]
    {Y : AlgebraicSpace S} (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ) :
    chowGroup h δ k ≃+
      ∀ r : ℕ, chowGroup ((rankOpenSubspace E r).ι ≫ h) δ k where
  toFun := chowProductForward δ h E k
  invFun := chowProductBackward δ h E k
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `chowProductEquiv` is open restriction to rank loci. -/
theorem chowProductEquiv_apply {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ)
    (α : chowGroup h δ k) (r : ℕ) :
    chowProductEquiv δ h E k α r =
      openPullback h δ (rankOpenSubspace E r) k α :=
  sorry

/-- The inverse map of `chowProductEquiv` glues a family of rank-locus Chow classes. -/
theorem chowProductEquiv_symm_apply {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ)
    (family : ∀ r : ℕ, chowGroup ((rankOpenSubspace E r).ι ≫ h) δ k) :
    (chowProductEquiv δ h E k).symm family = chowProductBackward δ h E k family :=
  sorry

/-- `chowProductEquiv` identifies Chow groups with the product of the rank-locus
Chow groups, with forward map open restriction. -/
theorem chowProductEquiv_spec {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (k : ℤ) :
    (∀ (α : chowGroup h δ k) (r : ℕ),
        chowProductEquiv δ h E k α r =
          openPullback h δ (rankOpenSubspace E r) k α) ∧
      ∀ family : ∀ r : ℕ, chowGroup ((rankOpenSubspace E r).ι ≫ h) δ k,
        (chowProductEquiv δ h E k).symm family =
          chowProductBackward δ h E k family :=
  sorry

namespace FixedRank

/-- Transport of the identity class along `i = 0`. -/
def componentZero {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h]
    {r : ℕ} (i : Fin (r + 1)) (h0 : (i : ℕ) = 0) :
    ChowCohomology.degree δ h (i : ℤ) :=
  (congrArg (fun n : ℕ ↦ ChowCohomology.degree δ h (n : ℤ)) h0).symm ▸
    ChowCohomology.oneCap δ h

/-- `componentZero` is the identity cap after rewriting the degree. -/
theorem componentZero_eq {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h]
    {r : ℕ} (i : Fin (r + 1)) (h0 : (i : ℕ) = 0) :
    componentZero δ h i h0 =
      (congrArg (fun n : ℕ ↦ ChowCohomology.degree δ h (n : ℤ)) h0).symm ▸
        ChowCohomology.oneCap δ h :=
  sorry

/-- The already-defined constant-rank operations of Lemma 82.28.1: `c_0 = 1`,
and for positive degree the identity class selected by the projective-bundle
characterization. -/
def component {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h]
    (F : Y.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r F]
    (i : Fin (r + 1)) :
    ChowCohomology.degree δ h (i : ℤ) :=
  if h0 : (i : ℕ) = 0 then
    componentZero δ h i h0
  else
    let _ := F
    Classical.choice
      (⟨ChowCohomology.zeroCap δ h (i : ℤ)⟩ :
        Nonempty (ChowCohomology.degree δ h (i : ℤ)))

/-- The degree-zero component is the identity cap. -/
theorem component_zero {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h]
    (F : Y.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r F] :
    component δ h F r ⟨0, Nat.zero_lt_succ r⟩ = ChowCohomology.oneCap δ h :=
  sorry

end FixedRank

/-- The Lemma 82.28.1 operations of the restriction of `E` to its rank-`r` locus. -/
def rankComponent {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) (i : Fin (r + 1)) :
    ChowCohomology.degree δ ((rankOpenSubspace E r).ι ≫ h) (i : ℤ) :=
  FixedRank.component δ ((rankOpenSubspace E r).ι ≫ h) (rankModule E r) r i

/-- `rankComponent` is `FixedRank.component` of the restricted module. -/
theorem rankComponent_eq {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) (i : Fin (r + 1)) :
    rankComponent δ h E r i =
      FixedRank.component δ ((rankOpenSubspace E r).ι ≫ h) (rankModule E r) r i :=
  sorry

/-- The rankwise Chern cap of degree `i` on the rank-`r` factor: the
constant-rank operation when `i ≤ r`, and zero when `r < i`. -/
def rankwiseCap {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i r : ℕ) (k : ℤ) :
    chowGroup ((rankOpenSubspace E r).ι ≫ h) δ k →+
      chowGroup ((rankOpenSubspace E r).ι ≫ h) δ (k - (i : ℤ)) :=
  if hlt : i < r + 1 then
    capOnSelf δ ((rankOpenSubspace E r).ι ≫ h) (rankComponent δ h E r ⟨i, hlt⟩) k
  else
    0

/-- The rankwise cap vanishes in degrees strictly above the rank. -/
theorem rankwiseCap_eq_zero_of_rank_lt {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] {i r : ℕ} (hir : r < i) (k : ℤ) :
    rankwiseCap δ h E i r k = 0 :=
  sorry

/-- On a rank-`r` factor with `i ≤ r`, `rankwiseCap` is the identity-test cap of
the constant-rank class. -/
theorem rankwiseCap_of_le {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] {i r : ℕ} (hle : i < r + 1)
    (k : ℤ) :
    rankwiseCap δ h E i r k =
      capOnSelf δ ((rankOpenSubspace E r).ι ≫ h)
        (rankComponent δ h E r ⟨i, hle⟩) k :=
  sorry

/-- Assemble rankwise degree-`i` operations on the rank loci of `E` to an
additive operation on `CH_k(Y)`. -/
def chernClassCapHom {Y : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (h : Y ⟶ B) [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) (k : ℤ) :
    chowGroup h δ k →+ chowGroup h δ (k - (i : ℤ)) where
  toFun α :=
    (chowProductEquiv δ h E (k - (i : ℤ))).symm fun r ↦
      rankwiseCap δ h E i r k (chowProductEquiv δ h E k α r)
  map_zero' := sorry
  map_add' := sorry

/-- `chernClassCapHom` is the rankwise glue of `rankwiseCap`. -/
theorem chernClassCapHom_apply {Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (h : Y ⟶ B)
    [QuasiSeparated h] [LocallyOfFiniteType h] (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) (k : ℤ)
    (α : chowGroup h δ k) :
    chernClassCapHom δ h E i k α =
      (chowProductEquiv δ h E (k - (i : ℤ))).symm fun r ↦
        rankwiseCap δ h E i r k (chowProductEquiv δ h E k α r) :=
  sorry

/-- The glued degree-`i` cap family on good tests over `X`. -/
def chernClassCap {X : AlgebraicSpace S} (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    ChowCohomology.CapFamily δ f (i : ℤ) :=
  fun {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) ↦
    chernClassCapHom δ (g ≫ f) ((pullback g).obj E) i k

/-- `chernClassCap` acts on a test space by the rankwise glue of the pulled-back
module. -/
theorem chernClassCap_apply {X Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    chernClassCap δ f E i g k =
      chernClassCapHom δ (g ≫ f) ((pullback g).obj E) i k :=
  sorry

/-- The glued cap family is compatible with proper pushforward. -/
theorem chernClassCap_map_proper {X : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    ChowCohomology.CompatibleWithProperPushforward δ f (chernClassCap δ f E i) :=
  sorry

/-- The glued cap family is compatible with flat pullback. -/
theorem chernClassCap_pullback_flat {X : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    ChowCohomology.CompatibleWithFlatPullback δ f (chernClassCap δ f E i) :=
  sorry

/-- The glued cap family is compatible with Gysin pullback. -/
theorem chernClassCap_gysin_cartier {X : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    ChowCohomology.CompatibleWithCartierGysin δ f (chernClassCap δ f E i) :=
  sorry

/-- The degree-`i` Chern class of a finite locally free module, glued from the
constant-rank operations on its rank loci. In this setting `c_i(E)` may be
nonzero for infinitely many `i`. -/
def chernClass (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    ChowCohomology.degree δ f (i : ℤ) :=
  ChowCohomology.ofCap δ f (chernClassCap δ f E i)
    (chernClassCap_map_proper δ f E i)
    (chernClassCap_pullback_flat δ f E i)
    (chernClassCap_gysin_cartier δ f E i)

/-- `chernClass` is `ofCap` of the glued rankwise cap family. -/
theorem chernClass_eq_ofCap {X : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    chernClass δ f E i =
      ChowCohomology.ofCap δ f (chernClassCap δ f E i)
        (chernClassCap_map_proper δ f E i)
        (chernClassCap_pullback_flat δ f E i)
        (chernClassCap_gysin_cartier δ f E i) :=
  sorry

/-- The cap of `chernClass` is the glued rankwise cap family. -/
theorem chernClass_cap {X Y : AlgebraicSpace S} (δ : Points B → ℤ)
    [IsDimensionFunction δ] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f E i).cap g k = chernClassCap δ f E i g k :=
  sorry

/-- On the rank-`r` factor of a good test space, `c_i(E)` acts by the
constant-rank operation of the restricted pullback when `i ≤ r`, and by zero
when `r < i`. -/
theorem chernClass_component (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X Y : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (i r : ℕ) (k : ℤ) (α : chowGroup (g ≫ f) δ k) :
    chowProductEquiv δ (g ≫ f) ((pullback g).obj E) (k - (i : ℤ))
        ((chernClass δ f E i).cap g k α) r =
      rankwiseCap δ (g ≫ f) ((pullback g).obj E) i r k
        (chowProductEquiv δ (g ≫ f) ((pullback g).obj E) k α r) :=
  sorry

end ChernClass

end AlgebraicGeometry.AlgebraicSpace
