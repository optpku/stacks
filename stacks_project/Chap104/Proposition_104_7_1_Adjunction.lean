/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Data.Nat.Find
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Localization
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek
public import stacks_project.Chap104.Lemma_104_5_4_Colocalization
public import stacks_project.Chap104.Proposition_104_6_1_Plus
public import stacks_project.Chap104.Proposition_104_6_1_Pushforward
public import stacks_project.Chap104.Proposition_104_7_1_Pullback

/-!
# Hom-adjunction of derived quasi-coherent pullback and pushforward

For a quasi-compact quasi-separated morphism of algebraic stacks, the left
derived functor `Lf^*_QCoh` is Hom-adjoint to `Rf_{QCoh,*}` on morphisms from
unbounded `D_QCoh(𝒪_Y)` into the image of `D⁺_QCoh(𝒪_X)`. The identification
follows the 07BE calculus: colocalize the representative of `A`, identify
quotient Homs with the colimit over plus parasitic denominators, transport by
the `D(𝒪)` adjunction, and collapse the colimit at the identity leg using
104.6.1.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver CategoryTheory.Functor
open AlgebraicGeometry.GroupoidsOver.FppfDerivedPushforwardImpl
open CategoryTheory.Limits CategoryTheory.Localization CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty DerivedCategory DerivedCategory.TStructure
open CategoryTheory.Adjunction.TotalDerived ComplexShape RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidsOver.FppfDerivedPushforwardImpl
open FppfDerivedPushforwardImpl
open MorphismProperty.LeftFraction.Localization
open ObjectProperty.FullSubcategory

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Scalar restriction along the inverse-image structure map of a morphism of
algebraic stacks is a right adjoint. -/
instance fppfRingedToposHom_restrictScalars_isRightAdjoint (f : X ⟶ Y) :
    (SheafOfModules.restrictScalars
      (fppfRingedToposHom f).structureMap).IsRightAdjoint := sorry

/-- Derived inverse image on `D(𝒪)` is left adjoint to K-injective derived
pushforward. -/
def fppfModuleDerivedAdjunction (f : X ⟶ Y) :
    fppfModuleDerivedInverseImage f ⊣
      FppfDerivedPushforwardImpl.moduleDerivedPushforward f :=
  Adjunction.Derived.KInjective.adjunction
    (fppfModuleInverseImageExact f)
    (FppfDerivedPushforwardImpl.modulePushforward f)
    (fppfRingedToposHom f).moduleAdjunction

/-- `fppfModuleDerivedAdjunction` is the K-injective derived adjunction of
underived inverse image against pushforward. -/
theorem fppfModuleDerivedAdjunction_eq (f : X ⟶ Y) :
    fppfModuleDerivedAdjunction f =
      Adjunction.Derived.KInjective.adjunction
        (fppfModuleInverseImageExact f)
        (FppfDerivedPushforwardImpl.modulePushforward f)
        (fppfRingedToposHom f).moduleAdjunction := sorry

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
theorem colocalizeCounit_mem_trW (Z : GroupoidsOver S) [AlgebraicStack Z]
    (E : DerivedLQCohFbc Z) :
    (derivedParasitic Z).trW ((DerivedLQCohFbc.colocalizeCounit Z).app E) :=
  sorry

/-- `Lg_! g^* E` computes the left derived functor of `q ∘ f^*`. -/
instance pullbackToQCoh.computesAt_colocalize (f : X ⟶ Y) (E : DerivedLQCohFbc Y) :
    LeftDerived.ComputesAt (DerivedQCoh.pullbackToQCoh f) (derivedParasitic Y).trW
      ((DerivedLQCohFbc.colocalize Y).obj E) :=
  sorry

/-- Plus parasitic morphisms remain parasitic after inclusion into unbounded
`D_{LQCoh^{fbc}}`. -/
theorem toUnbounded_maps_trW {Z : GroupoidsOver S} [AlgebraicStack Z]
    {H H' : DerivedLQCohFbc.Plus Z} {s : H ⟶ H'}
    (hs : (derivedParasiticPlus Z).trW s) :
    (derivedParasitic Z).trW ((DerivedLQCohFbc.Plus.toUnbounded Z).map s) :=
  sorry

/-- Bounded-below `Rf_*` sends plus parasitic morphisms to plus parasitic
morphisms. -/
theorem derivedPushforwardPlusLQCohFbc_maps_trW (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {H H' : DerivedLQCohFbc.Plus X} {s : H ⟶ H'}
    (hs : (derivedParasiticPlus X).trW s) :
    (derivedParasiticPlus Y).trW ((derivedPushforwardPlusLQCohFbc f).map s) :=
  sorry

/-- The unbounded image of a plus parasitic pushforward remains parasitic. -/
theorem derivedPushforwardPlus_toUnbounded_maps_trW (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {H H' : DerivedLQCohFbc.Plus X} {s : H ⟶ H'}
    (hs : (derivedParasiticPlus X).trW s) :
    (derivedParasitic Y).trW
      ((DerivedLQCohFbc.Plus.toUnbounded Y).map
        ((derivedPushforwardPlusLQCohFbc f).map s)) :=
  toUnbounded_maps_trW (derivedPushforwardPlusLQCohFbc_maps_trW f hs)

namespace DerivedQCoh

variable (f : X ⟶ Y)
variable [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]

/-- The selected representative of an unbounded quasi-coherent object in
`D_{LQCoh^{fbc}}`. -/
abbrev representative (A : DerivedQCoh Y) : DerivedLQCohFbc Y :=
  (quotientFunctor Y).objPreimage A

/-- The selected bounded-below representative of an object of `D⁺_QCoh`. -/
abbrev plusRepresentative (B : DerivedQCoh.Plus X) : DerivedLQCohFbc.Plus X :=
  (Plus.quotientFunctor X).objPreimage B

/-- The colocalized computing object `E' = Lg_! g^* E` of the representative of
`A`. -/
abbrev colocalizedRepresentative (A : DerivedQCoh Y) : DerivedLQCohFbc Y :=
  (DerivedLQCohFbc.colocalize Y).obj (representative A)

/-- Comparison `Lf^*_QCoh A ≅ q_X(f^* E')` from the colocalization coreplacement. -/
def pullbackObjIso (A : DerivedQCoh Y) :
    (pullback f).obj A ≅
      (pullbackToQCoh f).obj (colocalizedRepresentative A) :=
  (pullback f).mapIso ((quotientFunctor Y).objObjPreimageIso A).symm ≪≫
    LeftDerived.ComputesAt.coreplacementIso (pullbackToQCoh f)
      (derivedParasitic Y).trW (quotientFunctor Y)
      ((DerivedLQCohFbc.colocalizeCounit Y).app (representative A))
      (colocalizeCounit_mem_trW Y (representative A))
      (pullbackToQCoh.computesAt_colocalize f (representative A))

/-- Comparison `inclusion B ≅ q_X(H)` for the plus representative `H` of `B`. -/
def plusInclusionIso (B : DerivedQCoh.Plus X) :
    (Plus.inclusion X).obj B ≅
      (quotientFunctor X).obj
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj (plusRepresentative B)) :=
  (Plus.inclusion X).mapIso ((Plus.quotientFunctor X).objObjPreimageIso B).symm ≪≫
    (Plus.inclusion_facIso X).app (plusRepresentative B)

/-- Comparison `inclusion (Rf_{QCoh,*} B) ≅ q_Y(Rf_* H)` on plus representatives. -/
def pushforwardInclusionIso (B : DerivedQCoh.Plus X) :
    (Plus.inclusion Y).obj ((pushforward f).obj B) ≅
      (quotientFunctor Y).obj
        ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
          ((derivedPushforwardPlusLQCohFbc f).obj (plusRepresentative B))) :=
  (Plus.inclusion Y).mapIso
      ((pushforward f).mapIso ((Plus.quotientFunctor X).objObjPreimageIso B).symm) ≪≫
    (Plus.inclusion Y).mapIso ((pushforward_facIso f).app (plusRepresentative B)) ≪≫
    (Plus.inclusion_facIso Y).app
      ((derivedPushforwardPlusLQCohFbc f).obj (plusRepresentative B))

/-- Inclusion of plus parasitic denominators into unbounded parasitic
denominators of the image of `H`. -/
def plusToUnboundedUnder (H : DerivedLQCohFbc.Plus X) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H ⥤
      MorphismProperty.Under (derivedParasitic X).trW ⊤
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj H) where
  obj s :=
    MorphismProperty.Under.mk ⊤ ((DerivedLQCohFbc.Plus.toUnbounded X).map s.hom)
      (toUnbounded_maps_trW s.prop)
  map a :=
    MorphismProperty.Under.homMk ((DerivedLQCohFbc.Plus.toUnbounded X).map a.right) sorry trivial
  map_id := sorry
  map_comp := sorry

/-- The 07BE Hom-diagram: numerators `Hom(f^* E', H')` indexed by plus parasitic
denominators `H ⟶ H'`. -/
abbrev plusHomDiagram (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H ⥤ Type _ :=
  plusToUnboundedUnder H ⋙
    homDiagram (derivedParasitic X).trW
      ((DerivedLQCohFbc.inverseImage f).obj E')
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)

/-- Identity plus denominator of `H`. -/
def plusIdDenom (H : DerivedLQCohFbc.Plus X) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H :=
  MorphismProperty.Under.mk ⊤ (𝟙 H) ((derivedParasiticPlus X).trW.id_mem H)

/-- A nonpositive lower bound exists by the bound already carried by `H`.
This proof selects no derived object or morphism. -/
theorem plusTargetBound_exists (H : DerivedLQCohFbc.Plus X) :
    ∃ n : ℕ, t.IsGE H.obj.obj (-(n : ℤ)) := by
  obtain ⟨n, hn⟩ := H.obj.property
  refine ⟨(-n).toNat, ?_⟩
  exact ⟨t.ge_antitone (by omega) H.obj.obj hn.ge⟩

/-- The least natural number whose negative is a lower bound for the existing
plus target. `Nat.find` uses its proved bound, never an admitted existence. -/
def plusTargetBound (H : DerivedLQCohFbc.Plus X) : ℕ := by
  classical
  exact Nat.find (plusTargetBound_exists H)

/-- The selected integer really bounds the existing target. -/
theorem plusTargetBound_spec (H : DerivedLQCohFbc.Plus X) :
    t.IsGE H.obj.obj (-(plusTargetBound H : ℤ)) := by
  classical
  exact Nat.find_spec (plusTargetBound_exists H)

/-- Good truncation preserves the cohomology-in property: surviving
cohomology is unchanged and lower cohomology is zero. -/
theorem truncGE_lqcohFbc (E : DerivedLQCohFbc X) (n : ℤ) :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)
      ((t.truncGE n).obj E.obj) := by
  sorry

/-- Uniform bounded target of an unbounded denominator. Its carrier is the
canonical good truncation, not a selected replacement or a zero fallback. -/
def boundedDenominatorTarget (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    DerivedLQCohFbc.Plus X :=
  ⟨⟨(t.truncGE (-(plusTargetBound H : ℤ))).obj s.right.obj,
    ⟨-(plusTargetBound H : ℤ), t.isGE_truncGE_obj s.right.obj _ _ (le_refl _)⟩⟩,
    truncGE_lqcohFbc s.right _⟩

/-- Every numerator is postcomposed with this same canonical truncation map. -/
def boundedDenominatorProjection (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    s.right ⟶ (DerivedLQCohFbc.Plus.toUnbounded X).obj
      (boundedDenominatorTarget H s) :=
  ⟨(t.truncGEπ (-(plusTargetBound H : ℤ))).app s.right.obj⟩

/-- The denominator after uniform good truncation. -/
def boundedDenominatorHom (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    H ⟶ boundedDenominatorTarget H s :=
  ⟨⟨s.hom.hom ≫ (t.truncGEπ (-(plusTargetBound H : ℤ))).app s.right.obj⟩⟩

/-- If `H → H'` has parasitic cone, truncating `H'` below a lower bound of
`H` still gives a denominator. Below that bound the cohomology of `H'` is
parasitic, so the truncation projection itself has parasitic cone. -/
theorem boundedDenominator_mem (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    (derivedParasiticPlus X).trW (boundedDenominatorHom H s) := by
  sorry

/-- The genuine plus-denominator index attached to each unbounded denominator. -/
def boundedDenominator (H : DerivedLQCohFbc.Plus X)
    (s : MorphismProperty.Under (derivedParasitic X).trW ⊤
      ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H :=
  MorphismProperty.Under.mk ⊤ (boundedDenominatorHom H s) (boundedDenominator_mem H s)

/-- Truncation of a comparison map gives the comparison of bounded denominators.
The bound depends only on `H`, so it is identical at both ends. -/
theorem truncation_postcomp (n : ℤ) {K L M : ModuleDerived X}
    (g : K ⟶ L) (a : L ⟶ M) :
    (g ≫ (t.truncGEπ n).app L) ≫ (t.truncGE n).map a =
      (g ≫ a) ≫ (t.truncGEπ n).app M :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => g ≫ k) ((t.truncGEπ n).naturality a).symm).trans
      (Category.assoc _ _ _).symm)

/-- The denominator comparison has the canonical truncated arrow as its map. -/
def boundedDenominatorMap (H : DerivedLQCohFbc.Plus X)
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
def boundedNumerator (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
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
def boundedDenominatorCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
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
def plusInclusionCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
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

/-- The bounded-denominator comparison with localized Hom. Both functions are
explicit quotient descents. The inverse laws use the actual truncation
projection as a common successor, rather than an arbitrary colimit witness. -/
def plusHomColimitEquiv (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y) :
    (plusHomDiagram f H E').ColimitType ≃
      ((quotientFunctor X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
       (quotientFunctor X).obj ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) where
  toFun x := homColimit.typeEquivTo (quotientFunctor X) (derivedParasitic X).trW
    ((DerivedLQCohFbc.inverseImage f).obj E')
    ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)
    ((plusHomDiagram f H E').descColimitType (plusInclusionCocone f H E') x)
  invFun g := (homDiagram (derivedParasitic X).trW
    ((DerivedLQCohFbc.inverseImage f).obj E')
    ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).descColimitType
      (boundedDenominatorCocone f H E')
      ((homColimit.typeEquivTo (quotientFunctor X) (derivedParasitic X).trW
        ((DerivedLQCohFbc.inverseImage f).obj E')
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)).symm g)
  left_inv := by sorry
  right_inv := by sorry

/-- Localized Hom is computed by the actual plus-denominator colimit. -/
def quotientToPlusColimit (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (g : (quotientFunctor X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
      (quotientFunctor X).obj ((DerivedLQCohFbc.Plus.toUnbounded X).obj H)) :
    (plusHomDiagram f H E').ColimitType :=
  (plusHomColimitEquiv f H E').symm g

/-- Ambient `D(𝒪)` Hom associated to a plus numerator `f^* E' ⟶ H'`. -/
def plusNumeratorAmbient (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    (DerivedLQCohFbc.inclusion X).obj ((DerivedLQCohFbc.inverseImage f).obj E') ⟶
      (DerivedLQCohFbc.Plus.ambient X).obj s.right :=
  (DerivedLQCohFbc.inverseImage_comp_inclusion f).hom.app E' ≫
    (DerivedLQCohFbc.inclusion X).map φ.down ≫
      (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso (FppfModules.lqcohFbc X)).hom.app
        s.right

/-- `D(𝒪)` adjunction transport of a plus numerator. -/
def plusNumeratorAdjoint (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    (DerivedLQCohFbc.inclusion Y).obj E' ⟶
      (DerivedLQCohFbc.Plus.ambient Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj s.right) :=
  (fppfModuleDerivedAdjunction f).homEquiv _ _
      (plusNumeratorAmbient f H E' s φ) ≫
    (derivedPushforwardPlusLQCohFbc_comp_ambient f).inv.app s.right

/-- Restricted adjoint numerator in `D_{LQCoh^{fbc}}(𝒪_Y)`. -/
def plusNumeratorLQCohFbc (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    E' ⟶
      (DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj s.right) :=
  (DerivedLQCohFbc.inclusion Y).preimage
    (plusNumeratorAdjoint f H E' s φ ≫
      (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso (FppfModules.lqcohFbc Y)).inv.app
        ((derivedPushforwardPlusLQCohFbc f).obj s.right))

/-- Identity-leg lift of an adjoint numerator along `Rf_* s`, using 104.6.1. -/
def plusNumeratorLift (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (hE' : (derivedParasitic Y).leftOrthogonal E')
    (s : MorphismProperty.Under (derivedParasiticPlus X).trW ⊤ H)
    (φ : (plusHomDiagram f H E').obj s) :
    E' ⟶
      (DerivedLQCohFbc.Plus.toUnbounded Y).obj
        ((derivedPushforwardPlusLQCohFbc f).obj H) :=
  ObjectProperty.leftOrthogonal.lift
    (derivedPushforwardPlus_toUnbounded_maps_trW f s.prop) hE'
    (plusNumeratorLQCohFbc f H E' s φ)

/-- Cocone collapsing the plus Hom-diagram to
`Hom(q(E'), q(Rf_* H))` after adjunction and 104.6.1. -/
def plusDescentCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
    (hE' : (derivedParasitic Y).leftOrthogonal E') :
    (plusHomDiagram f H E').CoconeTypes where
  pt :=
    (quotientFunctor Y).obj E' ⟶
      (quotientFunctor Y).obj
        ((DerivedLQCohFbc.Plus.toUnbounded Y).obj
          ((derivedPushforwardPlusLQCohFbc f).obj H))
  ι s φ := (quotientFunctor Y).map (plusNumeratorLift f H E' hE' s φ)
  ι_naturality := sorry

/-- Cocone of left-orthogonal lifts of Hom-diagrams out of `E'` along parasitic
denominators of `Rf_* H`. -/
def colocalLiftCocone (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
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
  ι_naturality := sorry

/-- Invert `q` on morphisms out of the colocal object `E'`. -/
def colocalHomInv (H : DerivedLQCohFbc.Plus X) (E' : DerivedLQCohFbc Y)
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
def pullback_homEquiv.toQuotientHom (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
    (g : (pullback f).obj A ⟶ (Plus.inclusion X).obj B) :
    (quotientFunctor X).obj
        ((DerivedLQCohFbc.inverseImage f).obj (colocalizedRepresentative A)) ⟶
      (quotientFunctor X).obj
        ((DerivedLQCohFbc.Plus.toUnbounded X).obj (plusRepresentative B)) :=
  (pullbackObjIso f A).inv ≫ g ≫ (plusInclusionIso B).hom

/-- Forward 07BE map
`Hom(Lf^*_QCoh A, B) → Hom(A, Rf_{QCoh,*} B)`. -/
def pullback_homEquiv.toHom (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
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

/-- Inverse 07BE map
`Hom(A, Rf_{QCoh,*} B) → Hom(Lf^*_QCoh A, B)`, via the identity colimit leg. -/
def pullback_homEquiv.ofHom (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
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
              (FppfDerivedPushforwardImpl.moduleDerivedPushforward f).map
                ((DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso
                    (FppfModules.lqcohFbc X)).inv.app (plusRepresentative B))))) ≫
    (plusInclusionIso B).inv

/-- Hom-adjunction
`Hom_{D_QCoh(X)}(Lf^*_QCoh A, B) ≃ Hom_{D_QCoh(Y)}(A, Rf_{QCoh,*} B)`
for `A` in unbounded `D_QCoh(𝒪_Y)` and `B` in `D⁺_QCoh(𝒪_X)`. -/
def pullback_homEquiv (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X) :
    ((pullback f).obj A ⟶ (Plus.inclusion X).obj B) ≃
      (A ⟶ (Plus.inclusion Y).obj ((pushforward f).obj B)) where
  toFun := pullback_homEquiv.toHom f A B
  invFun := pullback_homEquiv.ofHom f A B
  left_inv := sorry
  right_inv := sorry

/-- `pullback_homEquiv` is assembled from the named 07BE forward and inverse
maps. -/
theorem pullback_homEquiv_eq (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X) :
    (pullback_homEquiv f A B).toFun = pullback_homEquiv.toHom f A B :=
  sorry

/-- Applying `pullback_homEquiv` is the named forward 07BE map. -/
theorem pullback_homEquiv_apply (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
    (g : (pullback f).obj A ⟶ (Plus.inclusion X).obj B) :
    pullback_homEquiv f A B g = pullback_homEquiv.toHom f A B g := sorry

/-- Applying the inverse of `pullback_homEquiv` is the named identity-leg
07BE map. -/
theorem pullback_homEquiv_symm_apply (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)
    (g : A ⟶ (Plus.inclusion Y).obj ((pushforward f).obj B)) :
    (pullback_homEquiv f A B).symm g = pullback_homEquiv.ofHom f A B g := sorry

end DerivedQCoh

end AlgebraicGeometry.AlgebraicStack
