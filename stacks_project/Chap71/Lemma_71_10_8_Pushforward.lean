/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_10_8_Stalk

/-!
# Pushforwards of stalk local rings at codimension-zero points

The sheaf `j_{η,*} 𝒪_{X,η}` is the small-étale commutative-ring pushforward of the structure
sheaf of `Spec(𝒪_{X,η})`, universe-lifted to `CommRingCat.{u+1}`. The product of these sheaves
over `η ∈ X^0` is the canonical comparison object for `𝒦_X`. The corresponding module
pushforwards `j_{η,*} ℱ_η` are formed by pullback/pushforward on `X.Modules` and then universe
lift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Sections of `ringPushforward` of a structure sheaf multiply commutatively. -/
theorem structureSheafPushforward_mul_comm {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (U : (smallEtaleSite Y)ᵒᵖ)
    (a b : ((ringPushforward f).obj (structureSheaf X)).obj.obj U) : a * b = b * a :=
  sorry

/-- The commutative ring structure on sections of `f_* 𝒪_X`. -/
@[reducible]
noncomputable def commRingOfStructureSheafPushforward {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : (smallEtaleSite Y)ᵒᵖ) :
    CommRing (((ringPushforward f).obj (structureSheaf X)).obj.obj U) where
  mul_comm := structureSheafPushforward_mul_comm f U

/-- `commRingOfStructureSheafPushforward` uses the original ring operations. -/
theorem commRingOfStructureSheafPushforward_toRing {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : (smallEtaleSite Y)ᵒᵖ)
    [h : Ring (((ringPushforward f).obj (structureSheaf X)).obj.obj U)] :
    (commRingOfStructureSheafPushforward f U).toRing = h :=
  sorry

/-- The `RingCat`-valued sheaf `f_* 𝒪_X`. -/
noncomputable def structureSheafPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Sheaf (smallEtaleTopology Y) RingCat.{u} :=
  (ringPushforward f).obj (structureSheaf X)

/-- `structureSheafPushforward` is `ringPushforward` of `structureSheaf`. -/
theorem structureSheafPushforward_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    structureSheafPushforward f = (ringPushforward f).obj (structureSheaf X) :=
  sorry

/-- The small-étale pushforward of the structure sheaf of `Spec(𝒪_{X,η})` along `j_η`, as a
presheaf of commutative rings in universe `u`, obtained from the `ringPushforward` composite
on the underlying `RingCat`-valued structure sheaf. -/
noncomputable def codimZeroStalkPushforwardPresheafUnlifted {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U :=
    @CommRingCat.of
      ((structureSheafPushforward (codimZeroStalkMap hweak hmono η)).obj.obj U)
      (commRingOfStructureSheafPushforward (codimZeroStalkMap hweak hmono η) U)
  map {U V} g :=
    @CommRingCat.ofHom
      ((structureSheafPushforward (codimZeroStalkMap hweak hmono η)).obj.obj U)
      ((structureSheafPushforward (codimZeroStalkMap hweak hmono η)).obj.obj V)
      (commRingOfStructureSheafPushforward (codimZeroStalkMap hweak hmono η) U)
      (commRingOfStructureSheafPushforward (codimZeroStalkMap hweak hmono η) V)
      ((structureSheafPushforward (codimZeroStalkMap hweak hmono η)).obj.map g).hom
  map_id := sorry
  map_comp := sorry

/-- The value of `codimZeroStalkPushforwardPresheafUnlifted` at `U` is the commutative ring of
sections of `j_{η,*} 𝒪_{X,η}`. -/
theorem codimZeroStalkPushforwardPresheafUnlifted_obj {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) (U : (smallEtaleSite X)ᵒᵖ) :
    (codimZeroStalkPushforwardPresheafUnlifted hweak hmono η).obj U =
      @CommRingCat.of
        ((structureSheafPushforward (codimZeroStalkMap hweak hmono η)).obj.obj U)
        (commRingOfStructureSheafPushforward (codimZeroStalkMap hweak hmono η) U) :=
  sorry

/-- The unlifted pushforward presheaf `j_{η,*} 𝒪_{X,η}` is a sheaf. -/
theorem codimZeroStalkPushforwardPresheafUnlifted_isSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    Presheaf.IsSheaf (smallEtaleTopology X)
      (codimZeroStalkPushforwardPresheafUnlifted hweak hmono η) :=
  sorry

/-- The small-étale sheaf `j_{η,*} 𝒪_{X,η}` before universe lift, obtained from
`ringPushforward` of the structure sheaf of `Spec(𝒪_{X,η})`. -/
noncomputable def codimZeroStalkPushforwardSheafUnlifted {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  ⟨codimZeroStalkPushforwardPresheafUnlifted hweak hmono η,
    codimZeroStalkPushforwardPresheafUnlifted_isSheaf hweak hmono η⟩

/-- The underlying presheaf of `codimZeroStalkPushforwardSheafUnlifted` is
`codimZeroStalkPushforwardPresheafUnlifted`. -/
theorem codimZeroStalkPushforwardSheafUnlifted_obj {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    (codimZeroStalkPushforwardSheafUnlifted hweak hmono η).obj =
      codimZeroStalkPushforwardPresheafUnlifted hweak hmono η :=
  sorry


/-- The universe-lifted small-étale presheaf `j_{η,*} 𝒪_{X,η}`. -/
noncomputable def codimZeroStalkPushforwardPresheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  codimZeroStalkPushforwardPresheafUnlifted hweak hmono η ⋙
    CommRingCat.universeLift.{u, u + 1}

/-- `codimZeroStalkPushforwardPresheaf` is the universe lift of the unlifted pushforward
presheaf. -/
theorem codimZeroStalkPushforwardPresheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    codimZeroStalkPushforwardPresheaf hweak hmono η =
      codimZeroStalkPushforwardPresheafUnlifted hweak hmono η ⋙
        CommRingCat.universeLift.{u, u + 1} :=
  sorry

/-- The universe-lifted pushforward presheaf `j_{η,*} 𝒪_{X,η}` is a sheaf. -/
theorem codimZeroStalkPushforwardPresheaf_isSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    Presheaf.IsSheaf (smallEtaleTopology X)
      (codimZeroStalkPushforwardPresheaf hweak hmono η) :=
  sorry

/-- The sheaf `j_{η,*} 𝒪_{X,η}` on `X_étale`, obtained by pushing forward the structure sheaf
of `Spec(𝒪_{X,η})` and lifting to `CommRingCat.{u+1}`. -/
noncomputable def codimZeroStalkPushforwardSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ⟨codimZeroStalkPushforwardPresheaf hweak hmono η,
    codimZeroStalkPushforwardPresheaf_isSheaf hweak hmono η⟩

/-- The underlying presheaf of `codimZeroStalkPushforwardSheaf` is the universe-lifted
pushforward presheaf. -/
theorem codimZeroStalkPushforwardSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X) :
    (codimZeroStalkPushforwardSheaf hweak hmono η).obj =
      codimZeroStalkPushforwardPresheaf hweak hmono η :=
  sorry

/-- The product presheaf `∏_{η ∈ X^0} j_{η,*} 𝒪_{X,η}`, formed objectwise. -/
noncomputable def codimZeroStalkPushforwardProductPresheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U :=
    CommRingCat.of
      (∀ η : codimZeroPoints X,
        (codimZeroStalkPushforwardSheaf hweak hmono η).obj.obj U)
  map {U V} f :=
    CommRingCat.ofHom
      { toFun := fun s η ↦
          ((codimZeroStalkPushforwardSheaf hweak hmono η).obj.map f).hom (s η)
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The value of the product presheaf at `U` is the product of the values of
`j_{η,*} 𝒪_{X,η}`. -/
theorem codimZeroStalkPushforwardProductPresheaf_obj {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (codimZeroStalkPushforwardProductPresheaf hweak hmono).obj U =
      CommRingCat.of
        (∀ η : codimZeroPoints X,
          (codimZeroStalkPushforwardSheaf hweak hmono η).obj.obj U) :=
  sorry

/-- The product presheaf of stalk pushforwards is a sheaf. -/
theorem codimZeroStalkPushforwardProductPresheaf_isSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    Presheaf.IsSheaf (smallEtaleTopology X)
      (codimZeroStalkPushforwardProductPresheaf hweak hmono) :=
  sorry

/-- The product sheaf `∏_{η ∈ X^0} j_{η,*} 𝒪_{X,η}` on `X_étale`. -/
noncomputable def codimZeroStalkPushforwardProductSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ⟨codimZeroStalkPushforwardProductPresheaf hweak hmono,
    codimZeroStalkPushforwardProductPresheaf_isSheaf hweak hmono⟩

/-- The underlying presheaf of the product sheaf is the objectwise product of stalk
pushforwards. -/
theorem codimZeroStalkPushforwardProductSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    (codimZeroStalkPushforwardProductSheaf hweak hmono).obj =
      codimZeroStalkPushforwardProductPresheaf hweak hmono :=
  sorry

/-- The `𝒪_X`-module `j_{η,*} ℱ_η`, obtained by pulling `ℱ` back along `j_η` and pushing
forward. -/
noncomputable def codimZeroStalkPushforwardModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) (η : codimZeroPoints X) : X.Modules :=
  (Modules.pushforward (codimZeroStalkMap hweak hmono η)).obj
    ((Modules.pullback (codimZeroStalkMap hweak hmono η)).obj F)

/-- `codimZeroStalkPushforwardModule` is the composite of module pullback and pushforward along
`j_η`. -/
theorem codimZeroStalkPushforwardModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) (η : codimZeroPoints X) :
    codimZeroStalkPushforwardModule hweak hmono F η =
      (Modules.pushforward (codimZeroStalkMap hweak hmono η)).obj
        ((Modules.pullback (codimZeroStalkMap hweak hmono η)).obj F) :=
  sorry

/-- The universe-lifted module `j_{η,*} ℱ_η`. -/
noncomputable def codimZeroStalkPushforwardModuleLift {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) (η : codimZeroPoints X) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  Modules.liftModule (codimZeroStalkPushforwardModule hweak hmono F η)

/-- `codimZeroStalkPushforwardModuleLift` is the universe lift of
`codimZeroStalkPushforwardModule`. -/
theorem codimZeroStalkPushforwardModuleLift_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) (η : codimZeroPoints X) :
    codimZeroStalkPushforwardModuleLift hweak hmono F η =
      Modules.liftModule (codimZeroStalkPushforwardModule hweak hmono F η) :=
  sorry

/-- The product of the universe-lifted modules `j_{η,*} ℱ_η` over `η ∈ X^0`. -/
noncomputable def codimZeroStalkPushforwardProductModule {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  ∏ᶜ fun η : codimZeroPoints X ↦
    codimZeroStalkPushforwardModuleLift hweak hmono F η

/-- The product of stalk module pushforwards is the corresponding categorical product. -/
theorem codimZeroStalkPushforwardProductModule_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) :
    codimZeroStalkPushforwardProductModule hweak hmono F =
      ∏ᶜ fun η : codimZeroPoints X ↦
        codimZeroStalkPushforwardModuleLift hweak hmono F η :=
  sorry

/-- The coproduct of the universe-lifted modules `j_{η,*} ℱ_η` over `η ∈ X^0`. -/
noncomputable def codimZeroStalkPushforwardCoproductModule {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  ∐ fun η : codimZeroPoints X ↦
    codimZeroStalkPushforwardModuleLift hweak hmono F η

/-- The coproduct of stalk module pushforwards is the corresponding categorical coproduct. -/
theorem codimZeroStalkPushforwardCoproductModule_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) :
    codimZeroStalkPushforwardCoproductModule hweak hmono F =
      ∐ fun η : codimZeroPoints X ↦
        codimZeroStalkPushforwardModuleLift hweak hmono F η :=
  sorry

/-- Because `X^0` is locally finite, the coproduct of the modules `j_{η,*} ℱ_η` is isomorphic
to their product. -/
theorem codimZeroStalkPushforwardCoproduct_isIsomorphic_product {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) :
    IsIsomorphic (codimZeroStalkPushforwardCoproductModule hweak hmono F)
      (codimZeroStalkPushforwardProductModule hweak hmono F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

