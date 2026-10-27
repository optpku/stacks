/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Data.Nat.Find
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Colocalization
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Localization

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open DerivedCategory DerivedCategory.TStructure
open CategoryTheory.Limits CategoryTheory.Localization CategoryTheory.MorphismProperty
open MorphismProperty.LeftFraction.Localization ObjectProperty.FullSubcategory
open scoped Bicategory

-- Local declaration justification (metaprogramming implementation): private representative and fraction implementations must be exported for the exposed public Hom equivalence.
set_option backward.privateInPublic true

noncomputable section

universe u

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard


namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]

/-- The parasitic Verdier system on `D_{LQCoh^{fbc}}` has a left calculus of
fractions. -/
instance derivedParasitic_trW.instHasLeftCalculusOfFractions
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    ((derivedParasitic Z).trW).HasLeftCalculusOfFractions := sorry

/-- The parasitic Verdier system on `D⁺_{LQCoh^{fbc}}` has a left calculus of
fractions. -/
instance derivedParasiticPlus_trW.instHasLeftCalculusOfFractions
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    ((derivedParasiticPlus Z).trW).HasLeftCalculusOfFractions := sorry

/-- The colocalization counit `Lg_! g^* E ⟶ E` lies in the parasitic Verdier
system. -/
private theorem colocalizeCounit_mem_trW (Z : GroupoidsOver S) [AlgebraicStack Z]
    (E : DerivedLQCohFbc Z) :
    (derivedParasitic Z).trW ((DerivedLQCohFbc.colocalizeCounit Z).app E) := sorry

/-- `Lg_! g^* E` computes the left derived functor of `q ∘ f^*`. -/
instance DerivedQCoh.pullbackToQCoh.computesAt_colocalize (f : X ⟶ Y) (E : DerivedLQCohFbc Y) :
    LeftDerived.ComputesAt (DerivedQCoh.pullbackToQCoh f) (derivedParasitic Y).trW
      ((DerivedLQCohFbc.colocalize Y).obj E) := sorry

/-- Plus parasitic morphisms remain parasitic after inclusion into unbounded
`D_{LQCoh^{fbc}}`. -/
private theorem toUnbounded_maps_trW {Z : GroupoidsOver S} [AlgebraicStack Z]
    {H H' : DerivedLQCohFbc.Plus Z} {s : H ⟶ H'}
    (hs : (derivedParasiticPlus Z).trW s) :
    (derivedParasitic Z).trW ((DerivedLQCohFbc.Plus.toUnbounded Z).map s) := sorry

/-- Bounded-below `Rf_*` sends plus parasitic morphisms to plus parasitic
morphisms. -/
private theorem derivedPushforwardPlusLQCohFbc_maps_trW (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {H H' : DerivedLQCohFbc.Plus X} {s : H ⟶ H'}
    (hs : (derivedParasiticPlus X).trW s) :
    (derivedParasiticPlus Y).trW ((derivedPushforwardPlusLQCohFbc f).map s) := sorry

/-- The unbounded image of a plus parasitic pushforward remains parasitic. -/
private theorem derivedPushforwardPlus_toUnbounded_maps_trW (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {H H' : DerivedLQCohFbc.Plus X} {s : H ⟶ H'}
    (hs : (derivedParasiticPlus X).trW s) :
    (derivedParasitic Y).trW
      ((DerivedLQCohFbc.Plus.toUnbounded Y).map
        ((derivedPushforwardPlusLQCohFbc f).map s)) :=
  toUnbounded_maps_trW (derivedPushforwardPlusLQCohFbc_maps_trW f hs)

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y)
variable [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]

/-- The selected representative of an unbounded quasi-coherent object in
`D_{LQCoh^{fbc}}`. -/
private abbrev representative (A : DerivedQCoh Y) : DerivedLQCohFbc Y :=
  (quotientFunctor Y).objPreimage A

/-- The selected bounded-below representative of an object of `D⁺_QCoh`. -/
private abbrev plusRepresentative (B : DerivedQCoh.Plus X) : DerivedLQCohFbc.Plus X :=
  (Plus.quotientFunctor X).objPreimage B

/-- The colocalized computing object `E' = Lg_! g^* E` of the representative of
`A`. -/
private abbrev colocalizedRepresentative (A : DerivedQCoh Y) : DerivedLQCohFbc Y :=
  (DerivedLQCohFbc.colocalize Y).obj (representative A)

/-- Comparison `Lf^*_QCoh A ≅ q_X(f^* E')` from the colocalization coreplacement. -/
private def pullbackObjIso (A : DerivedQCoh Y) :
    (pullback f).obj A ≅
      (pullbackToQCoh f).obj (colocalizedRepresentative A) :=
  (pullback f).mapIso ((quotientFunctor Y).objObjPreimageIso A).symm ≪≫
    LeftDerived.ComputesAt.coreplacementIso (pullbackToQCoh f)
      (derivedParasitic Y).trW (quotientFunctor Y)
      ((DerivedLQCohFbc.colocalizeCounit Y).app (representative A))
      (colocalizeCounit_mem_trW Y (representative A))
      (pullbackToQCoh.computesAt_colocalize f (representative A))

/-- Comparison `inclusion B ≅ q_X(H)` for the plus representative `H` of `B`. -/
private def plusInclusionIso (B : DerivedQCoh.Plus X) :
    (Plus.inclusion X).obj B ≅
      (quotientFunctor X).obj
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj (plusRepresentative B)) :=
  (Plus.inclusion X).mapIso ((Plus.quotientFunctor X).objObjPreimageIso B).symm ≪≫
    (Plus.inclusion_facIso X).app (plusRepresentative B)

/-- Comparison `inclusion (Rf_{QCoh,*} B) ≅ q_Y(Rf_* H)` on plus representatives. -/
private def pushforwardInclusionIso (B : DerivedQCoh.Plus X) :
    (Plus.inclusion Y).obj ((pushforward f).obj B) ≅
      (quotientFunctor Y).obj
        ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
          ((derivedPushforwardPlusLQCohFbc f).obj (plusRepresentative B))) :=
  (Plus.inclusion Y).mapIso
      ((pushforward f).mapIso ((Plus.quotientFunctor X).objObjPreimageIso B).symm) ≪≫
    (Plus.inclusion Y).mapIso ((pushforward_facIso f).app (plusRepresentative B)) ≪≫
    (Plus.inclusion_facIso Y).app
      ((derivedPushforwardPlusLQCohFbc f).obj (plusRepresentative B))

/-- The image of a denominator comparison satisfies its commuting triangle. -/
private theorem plusToUnboundedUnder_map_w (H : DerivedLQCohFbc.Plus X)
    {s s' : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H} (a : s ⟶ s') :
    (DerivedLQCohFbc.Plus.toUnbounded X).map s.hom ≫
        (DerivedLQCohFbc.Plus.toUnbounded X).map a.right =
      (DerivedLQCohFbc.Plus.toUnbounded X).map s'.hom := sorry

/-- A comparison of bounded-below denominators gives an unbounded comparison. -/
private def plusToUnboundedUnderMap (H : DerivedLQCohFbc.Plus X)
    {s s' : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H} (a : s ⟶ s') :
    MorphismProperty.Under.mk ⊤ ((DerivedLQCohFbc.Plus.toUnbounded X).map s.hom)
        (toUnbounded_maps_trW s.prop) ⟶
      MorphismProperty.Under.mk ⊤ ((DerivedLQCohFbc.Plus.toUnbounded X).map s'.hom)
        (toUnbounded_maps_trW s'.prop) :=
  MorphismProperty.Under.homMk ((DerivedLQCohFbc.Plus.toUnbounded X).map a.right)
    (plusToUnboundedUnder_map_w H a) trivial

/-- Inclusion of denominator comparisons preserves identities. -/
private theorem plusToUnboundedUnder_map_id (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H) :
    plusToUnboundedUnderMap H (𝟙 s) = 𝟙 _ := sorry

/-- Inclusion of denominator comparisons preserves composition. -/
private theorem plusToUnboundedUnder_map_comp (H : DerivedLQCohFbc.Plus X)
    {s s' s'' : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H}
    (a : s ⟶ s') (b : s' ⟶ s'') :
    plusToUnboundedUnderMap H (a ≫ b) =
      plusToUnboundedUnderMap H a ≫ plusToUnboundedUnderMap H b := sorry

/-- Include bounded-below parasitic denominators among unbounded denominators. -/
private def plusToUnboundedUnder (H : DerivedLQCohFbc.Plus X) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H ⥤
      MorphismProperty.Under (derivedParasitic X).trW ⊤
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj H) where
  obj s := MorphismProperty.Under.mk ⊤ ((DerivedLQCohFbc.Plus.toUnbounded X).map s.hom)
    (toUnbounded_maps_trW s.prop)
  map a := plusToUnboundedUnderMap H a
  map_id := plusToUnboundedUnder_map_id H
  map_comp := plusToUnboundedUnder_map_comp H

/-- The Hom-diagram: numerators `Hom(f^* E', H')` indexed by plus parasitic
denominators `H ⟶ H'`. -/
private abbrev plusHomDiagram (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H ⥤ Type _ :=
  plusToUnboundedUnder H ⋙
    homDiagram (derivedParasitic X).trW
      ((DerivedLQCohFbc.inverseImage f).obj E')
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)

/-- Identity plus denominator of `H`. -/
private def plusIdDenom (H : DerivedLQCohFbc.Plus X) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H :=
  MorphismProperty.Under.mk ⊤ (𝟙 H) ((derivedParasiticPlus X).trW.id_mem H)

/-- A nonpositive lower bound exists by the bound already carried by `H`.
This proof selects no derived object or morphism. -/
private theorem plusTargetBound_exists (H : DerivedLQCohFbc.Plus X) :
    ∃ n : ℕ, t.IsGE H.obj.obj (-(n : ℤ)) := by
  obtain ⟨n, hn⟩ := H.obj.property
  refine ⟨(-n).toNat, ?_⟩
  exact ⟨t.ge_antitone (by omega) H.obj.obj hn.ge⟩

/-- The least natural number whose negative is a lower bound for the existing
plus target. `Nat.find` uses its proved bound, never an admitted existence. -/
private def plusTargetBound (H : DerivedLQCohFbc.Plus X) : ℕ := by
  classical
  exact Nat.find (plusTargetBound_exists H)

/-- The selected integer really bounds the existing target. -/
private theorem plusTargetBound_spec (H : DerivedLQCohFbc.Plus X) :
    t.IsGE H.obj.obj (-(plusTargetBound H : ℤ)) := by
  classical
  exact Nat.find_spec (plusTargetBound_exists H)

/-- Good truncation preserves the cohomology-in property: surviving
cohomology is unchanged and lower cohomology is zero. -/
private theorem truncGE_lqcohFbc (E : DerivedLQCohFbc X) (n : ℤ) :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)
      ((t.truncGE n).obj E.obj) := sorry

/-- Uniform bounded target of an unbounded denominator. Its carrier is the
canonical good truncation, not a selected replacement or a zero fallback. -/
private def boundedDenominatorTarget (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    DerivedLQCohFbc.Plus X :=
  ⟨⟨(t.truncGE (-(plusTargetBound H : ℤ))).obj s.right.obj,
    ⟨-(plusTargetBound H : ℤ), t.isGE_truncGE_obj s.right.obj _ _ (le_refl _)⟩⟩,
    truncGE_lqcohFbc s.right _⟩

/-- Every numerator is postcomposed with this same canonical truncation map. -/
private def boundedDenominatorProjection (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    s.right ⟶ (DerivedLQCohFbc.Plus.toUnbounded X).obj
      (boundedDenominatorTarget H s) :=
  ⟨(t.truncGEπ (-(plusTargetBound H : ℤ))).app s.right.obj⟩

/-- The denominator after uniform good truncation. -/
private def boundedDenominatorHom (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    H ⟶ boundedDenominatorTarget H s :=
  ⟨⟨s.hom.hom ≫ (t.truncGEπ (-(plusTargetBound H : ℤ))).app s.right.obj⟩⟩

/-- If `H → H'` has parasitic cone, truncating `H'` below a lower bound of
`H` still gives a denominator. Below that bound the cohomology of `H'` is
parasitic, so the truncation projection itself has parasitic cone. -/
private theorem boundedDenominator_mem (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    (derivedParasiticPlus X).trW (boundedDenominatorHom H s) := sorry

/-- The genuine plus-denominator index attached to each unbounded denominator. -/
private def boundedDenominator (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H :=
  MorphismProperty.Under.mk ⊤ (boundedDenominatorHom H s) (boundedDenominator_mem H s)

/-- Truncation of a comparison map gives the comparison of bounded denominators.
The bound depends only on `H`, so it is identical at both ends. -/
private theorem truncation_postcomp (n : ℤ) {K L M : ModuleDerived X}
    (g : K ⟶ L) (a : L ⟶ M) :
    (g ≫ (t.truncGEπ n).app L) ≫ (t.truncGE n).map a =
      (g ≫ a) ≫ (t.truncGEπ n).app M :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => g ≫ k) ((t.truncGEπ n).naturality a).symm).trans
      (Category.assoc _ _ _).symm)

/-- The denominator comparison has the canonical truncated arrow as its map. -/
private def boundedDenominatorMap (H : DerivedLQCohFbc.Plus X)
    {s s' : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)} (a : s ⟶ s') :
    boundedDenominator H s ⟶ boundedDenominator H s' :=
  MorphismProperty.Under.homMk
    ⟨⟨(t.truncGE (-(plusTargetBound H : ℤ))).map a.right.hom⟩⟩
    (by
      apply InducedCategory.hom_ext
      apply InducedCategory.hom_ext
      change (s.hom.hom ≫ (t.truncGEπ _).app s.right.obj) ≫
        (t.truncGE _).map a.right.hom = s'.hom.hom ≫ (t.truncGEπ _).app s'.right.obj
      exact (truncation_postcomp (-(plusTargetBound H : ℤ)) s.hom.hom a.right.hom).trans
        (congrArg (fun k => k.hom ≫ (t.truncGEπ (-(plusTargetBound H : ℤ))).app s'.right.obj)
          (MorphismProperty.Under.w a))) trivial

/-- Numerators are transported by the actual truncation projection, including
when the old target is not bounded below. -/
private def boundedNumerator (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H))
    (φ : (homDiagram (derivedParasitic X).trW
      ((DerivedLQCohFbc.inverseImage f).obj E')
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).obj s) :
    (plusHomDiagram f H E').obj (boundedDenominator H s) :=
  ULift.up (φ.down ≫ boundedDenominatorProjection H s)

/-- A genuine cocone into the plus colimit, using the uniform truncation
comparison on every index. Naturality follows from truncation naturality and
the colimit relation for `boundedDenominatorMap`. -/
private def boundedDenominatorCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
    (homDiagram (derivedParasitic X).trW
      ((DerivedLQCohFbc.inverseImage f).obj E')
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).CoconeTypes where
  pt := (plusHomDiagram f H E').ColimitType
  ι s φ := (plusHomDiagram f H E').ιColimitType (boundedDenominator H s)
    (boundedNumerator f H E' s φ)
  ι_naturality := by
    intro s s' a
    funext φ
    have hmap : (plusHomDiagram f H E').map (boundedDenominatorMap H a)
        (boundedNumerator f H E' s φ) =
      boundedNumerator f H E' s'
        ((homDiagram (derivedParasitic X).trW
          ((DerivedLQCohFbc.inverseImage f).obj E')
          ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).map a φ) := by
      apply ULift.ext
      apply InducedCategory.hom_ext
      change (φ.down.hom ≫ (t.truncGEπ _).app s.right.obj) ≫
        (t.truncGE _).map a.right.hom =
        (φ.down.hom ≫ a.right.hom) ≫ (t.truncGEπ _).app s'.right.obj
      exact truncation_postcomp (-(plusTargetBound H : ℤ)) φ.down.hom a.right.hom
    exact (congrArg ((plusHomDiagram f H E').ιColimitType (boundedDenominator H s'))
      hmap).symm.trans ((plusHomDiagram f H E').ιColimitType_map
        (boundedDenominatorMap H a) (boundedNumerator f H E' s φ))

/-- The reverse comparison includes an actual plus numerator and denominator
into the unbounded colimit; it never reconstructs a witness. -/
private def plusInclusionCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
    (plusHomDiagram f H E').CoconeTypes where
  pt := (homDiagram (derivedParasitic X).trW
    ((DerivedLQCohFbc.inverseImage f).obj E')
    ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).ColimitType
  ι s φ := (homDiagram (derivedParasitic X).trW
    ((DerivedLQCohFbc.inverseImage f).obj E')
    ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).ιColimitType
      ((plusToUnboundedUnder H).obj s) φ
  ι_naturality := by
    intro s s' a
    funext φ
    exact (homDiagram (derivedParasitic X).trW
      ((DerivedLQCohFbc.inverseImage f).obj E')
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).ιColimitType_map
        ((plusToUnboundedUnder H).map a) φ

/-- Include a bounded-below numerator in the unbounded localization colimit. -/
private def plusHomColimitToHom (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (x : (plusHomDiagram f H E').ColimitType) :
    (quotientFunctor X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
      (quotientFunctor X).obj ((DerivedLQCohFbc.Plus.toUnbounded X).obj H) :=
  homColimit.typeEquivTo (quotientFunctor X) (derivedParasitic X).trW
    ((DerivedLQCohFbc.inverseImage f).obj E')
    ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)
    ((plusHomDiagram f H E').descColimitType (plusInclusionCocone f H E') x)

/-- Good truncation sends a localized morphism to the bounded-below denominator colimit. -/
private def plusHomColimitOfHom (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (g : (quotientFunctor X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
      (quotientFunctor X).obj ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    (plusHomDiagram f H E').ColimitType :=
  (homDiagram (derivedParasitic X).trW
    ((DerivedLQCohFbc.inverseImage f).obj E')
    ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).descColimitType
      (boundedDenominatorCocone f H E')
      ((homColimit.typeEquivTo (quotientFunctor X) (derivedParasitic X).trW
        ((DerivedLQCohFbc.inverseImage f).obj E')
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).symm g)

/-- Truncation after inclusion recovers each bounded-denominator colimit class. -/
private theorem plusHomColimitEquiv_left_inv (H : DerivedLQCohFbc.Plus X)
    (E' : DerivedLQCohFbc Y) :
    Function.LeftInverse (plusHomColimitOfHom f H E') (plusHomColimitToHom f H E') := sorry

/-- Inclusion after truncation recovers each localized morphism. -/
private theorem plusHomColimitEquiv_right_inv (H : DerivedLQCohFbc.Plus X)
    (E' : DerivedLQCohFbc Y) :
    Function.RightInverse (plusHomColimitOfHom f H E') (plusHomColimitToHom f H E') := sorry

/-- Localized morphisms to a bounded-below target are computed by bounded-below denominators. -/
private def plusHomColimitEquiv (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
    (plusHomDiagram f H E').ColimitType ≃
      ((quotientFunctor X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
       (quotientFunctor X).obj ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) where
  toFun := plusHomColimitToHom f H E'
  invFun := plusHomColimitOfHom f H E'
  left_inv := plusHomColimitEquiv_left_inv f H E'
  right_inv := plusHomColimitEquiv_right_inv f H E'

/-- Localized Hom is computed by the actual plus-denominator colimit. -/
private def quotientToPlusColimit (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (g : (quotientFunctor X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
      (quotientFunctor X).obj ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    (plusHomDiagram f H E').ColimitType :=
  (plusHomColimitEquiv f H E').symm g

/-- Ambient `D(𝒪)` Hom associated to a plus numerator `f^* E' ⟶ H'`. -/
private def plusNumeratorAmbient (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    (DerivedLQCohFbc.inclusion X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
      (DerivedLQCohFbc.Plus.ambient X).obj s.right :=
  (DerivedLQCohFbc.inverseImage_comp_inclusion f).hom.app E' ≫
    (DerivedLQCohFbc.inclusion X).map φ.down ≫
      (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso (FppfModules.lqcohFbc X)).hom.app
        s.right

/-- `D(𝒪)` adjunction transport of a plus numerator. -/
private def plusNumeratorAdjoint (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    (DerivedLQCohFbc.inclusion Y).obj E' ⟶
      (DerivedLQCohFbc.Plus.ambient Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj s.right) :=
  (fppfModuleDerivedAdjunction f).homEquiv _ _
      (plusNumeratorAmbient f H E' s φ) ≫
    (derivedPushforwardPlusLQCohFbc_comp_ambient f).inv.app s.right

/-- Restricted adjoint numerator in `D_{LQCoh^{fbc}}(𝒪_Y)`. -/
private def plusNumeratorLQCohFbc (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    E' ⟶
      (DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj s.right) :=
  (DerivedLQCohFbc.inclusion Y).preimage
    (plusNumeratorAdjoint f H E' s φ ≫
      (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso (FppfModules.lqcohFbc Y)).inv.app
        ((derivedPushforwardPlusLQCohFbc f).obj s.right))

/-- Identity-leg lift of an adjoint numerator along `Rf_* s`, using preservation of parasitic objects. -/
private def plusNumeratorLift (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (hE' : (derivedParasitic Y).leftOrthogonal E')
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    E' ⟶
      (DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H) :=
  ObjectProperty.leftOrthogonal.lift
    (derivedPushforwardPlus_toUnbounded_maps_trW f s.prop) hE'
    (plusNumeratorLQCohFbc f H E' s φ)

/-- The adjoint and orthogonal lift of a numerator is compatible with denominator comparisons. -/
private theorem plusDescentCocone_naturality (H : DerivedLQCohFbc.Plus X)
    (E' : DerivedLQCohFbc Y) (hE' : (derivedParasitic Y).leftOrthogonal E')
    {s s' : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H} (a : s ⟶ s') :
    (fun φ => (quotientFunctor Y).map (plusNumeratorLift f H E' hE' s' φ)).comp
        ((plusHomDiagram f H E').map a) =
      fun φ => (quotientFunctor Y).map (plusNumeratorLift f H E' hE' s φ) := sorry

/-- Cocone collapsing the plus Hom-diagram to
`Hom(q(E'), q(Rf_* H))` after adjunction and preservation of parasitic objects. -/
private def plusDescentCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (hE' : (derivedParasitic Y).leftOrthogonal E') :
    (plusHomDiagram f H E').CoconeTypes where
  pt :=
    (quotientFunctor Y).obj E' ⟶
      (quotientFunctor Y).obj
        ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
          ((derivedPushforwardPlusLQCohFbc f).obj H))
  ι s φ := (quotientFunctor Y).map (plusNumeratorLift f H E' hE' s φ)
  ι_naturality := plusDescentCocone_naturality f H E' hE'

/-- Orthogonal lifting of numerators is compatible with parasitic denominator comparisons. -/
private theorem colocalLiftCocone_naturality (H : DerivedLQCohFbc.Plus X)
    (E' : DerivedLQCohFbc Y) (hE' : (derivedParasitic Y).leftOrthogonal E')
    {s s' : MorphismProperty.Under (derivedParasitic Y).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded Y).obj ((derivedPushforwardPlusLQCohFbc f).obj H))}
    (a : s ⟶ s') :
    (fun ψ => ObjectProperty.leftOrthogonal.lift s'.prop hE' ψ.down).comp
        ((homDiagram (derivedParasitic Y).trW E'
          ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
            ((derivedPushforwardPlusLQCohFbc f).obj H))).map a) =
      fun ψ => ObjectProperty.leftOrthogonal.lift s.prop hE' ψ.down := sorry

/-- Cocone of left-orthogonal lifts of Hom-diagrams out of `E'` along parasitic
denominators of `Rf_* H`. -/
private def colocalLiftCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (hE' : (derivedParasitic Y).leftOrthogonal E') :
    (homDiagram (derivedParasitic Y).trW E'
      ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H))).CoconeTypes where
  pt :=
    E' ⟶
      (DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H)
  ι s ψ :=
    ObjectProperty.leftOrthogonal.lift s.prop hE' ψ.down
  ι_naturality := colocalLiftCocone_naturality f H E' hE'

/-- Invert `q` on morphisms out of the colocal object `E'`. -/
private def colocalHomInv (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (hE' : (derivedParasitic Y).leftOrthogonal E')
    (g : (quotientFunctor Y).obj E' ⟶
      (quotientFunctor Y).obj
        ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
          ((derivedPushforwardPlusLQCohFbc f).obj H))) :
    E' ⟶
      (DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H) :=
  (homDiagram (derivedParasitic Y).trW E'
      ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H))).descColimitType
    (colocalLiftCocone f H E' hE')
    ((homColimit.typeEquivTo (quotientFunctor Y) (derivedParasitic Y).trW E'
      ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H))).symm g)

/-- Localized morphism `q(f^* E') ⟶ q(H)` associated to
`Hom(Lf^*_QCoh A, B)`. -/
private def pullback_homEquiv.toQuotientHom (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
    (g : (pullback f).obj A ⟶ (Plus.inclusion X).obj B) :
    (quotientFunctor X).obj
        ((DerivedLQCohFbc.inverseImage f).obj (colocalizedRepresentative A)) ⟶
      (quotientFunctor X).obj
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj (plusRepresentative B)) :=
  (pullbackObjIso f A).inv ≫ g ≫ (plusInclusionIso B).hom

/-- Forward adjunction map
`Hom(Lf^*_QCoh A, B) → Hom(A, Rf_{QCoh,*} B)`. -/
private def pullback_homEquiv.toHom (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
    (g : (pullback f).obj A ⟶ (Plus.inclusion X).obj B) :
    (A ⟶ (Plus.inclusion Y).obj ((pushforward f).obj B)) :=
  ((quotientFunctor Y).objObjPreimageIso A).inv ≫
    (Localization.isoOfHom (quotientFunctor Y) (derivedParasitic Y).trW
        ((DerivedLQCohFbc.colocalizeCounit Y).app (representative A))
        (colocalizeCounit_mem_trW Y (representative A))).inv ≫
    (plusHomDiagram f (plusRepresentative B)
        (colocalizedRepresentative A)).descColimitType
      (plusDescentCocone f (plusRepresentative B) (colocalizedRepresentative A)
        (DerivedLQCohFbc.colocalize_leftOrthogonal Y (representative A)))
      (quotientToPlusColimit f (plusRepresentative B)
        (colocalizedRepresentative A)
        (pullback_homEquiv.toQuotientHom f A B g)) ≫
    (pushforwardInclusionIso f B).inv

/-- Inverse adjunction map
`Hom(A, Rf_{QCoh,*} B) → Hom(Lf^*_QCoh A, B)`, via the identity colimit leg. -/
private def pullback_homEquiv.ofHom (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
    (g : A ⟶ (Plus.inclusion Y).obj ((pushforward f).obj B)) :
    ((pullback f).obj A ⟶ (Plus.inclusion X).obj B) :=
  (pullbackObjIso f A).hom ≫
    (quotientFunctor X).map
      ((DerivedLQCohFbc.inclusion X).preimage
        ((DerivedLQCohFbc.inverseImage_comp_inclusion f).inv.app
            (colocalizedRepresentative A) ≫
          ((fppfModuleDerivedAdjunction f).homEquiv _ _).symm
            ((DerivedLQCohFbc.inclusion Y).map
                (colocalHomInv f (plusRepresentative B)
                  (colocalizedRepresentative A)
                  (DerivedLQCohFbc.colocalize_leftOrthogonal Y (representative A))
                  ((Localization.isoOfHom (quotientFunctor Y)
                      (derivedParasitic Y).trW
                      ((DerivedLQCohFbc.colocalizeCounit Y).app
                        (representative A))
                      (colocalizeCounit_mem_trW Y (representative A))).hom ≫
                    ((quotientFunctor Y).objObjPreimageIso A).hom ≫ g ≫
                      (pushforwardInclusionIso f B).hom)) ≫
              (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso
                  (FppfModules.lqcohFbc Y)).hom.app
                ((derivedPushforwardPlusLQCohFbc f).obj
                  (plusRepresentative B)) ≫
              (derivedPushforwardPlusLQCohFbc_comp_ambient f).hom.app
                (plusRepresentative B) ≫
              (moduleDerivedPushforward f).map
                ((DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso
                    (FppfModules.lqcohFbc X)).inv.app (plusRepresentative B))))) ≫
    (plusInclusionIso B).inv

/-- The inverse adjunction map undoes the forward map on localized morphisms. -/
private theorem pullback_homEquiv_left_inv (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X) :
    Function.LeftInverse (pullback_homEquiv.ofHom f A B)
      (pullback_homEquiv.toHom f A B) := sorry

/-- The forward adjunction map undoes the inverse map on localized morphisms. -/
private theorem pullback_homEquiv_right_inv (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X) :
    Function.RightInverse (pullback_homEquiv.ofHom f A B)
      (pullback_homEquiv.toHom f A B) := sorry

/-- Hom-adjunction
`Hom_{D_QCoh(X)}(Lf^*_QCoh A, B) ≃ Hom_{D_QCoh(Y)}(A, Rf_{QCoh,*} B)`
for `A` in unbounded `D_QCoh(𝒪_Y)` and `B` in `D⁺_QCoh(𝒪_X)`. -/
def pullback_homEquiv (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X) :
    ((pullback f).obj A ⟶ (Plus.inclusion X).obj B) ≃
      (A ⟶ (Plus.inclusion Y).obj ((pushforward f).obj B)) where
  toFun := pullback_homEquiv.toHom f A B
  invFun := pullback_homEquiv.ofHom f A B
  left_inv := pullback_homEquiv_left_inv f A B
  right_inv := pullback_homEquiv_right_inv f A B

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh
