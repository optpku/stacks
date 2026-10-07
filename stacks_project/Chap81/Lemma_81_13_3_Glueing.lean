module

public import Mathlib.Data.Countable.Small
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap81.Lemma_81_13_1

/-!
# Coproduct glueing data for the kernel-pair coequalizer of `X' ⨿ Z`

In the proper-iso-over-complement situation, the coproduct `Y = X' ⨿ Z` and
the kernel-pair coequalizer of its structure map `Y ⟶ X` supply the space
`X₁` of Lemma 81.13.3, together with the lift of the closed immersion
`Z ⟶ X` through `X₁`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}

/-- The two-element family whose coproduct is `X' ⨿ Z`. -/
def closedFamily (f : X' ⟶ X) (i : Z ⟶ X) (b : Bool) : AlgebraicSpace S :=
  match b with
  | false => X'
  | true => Z

/-- The `false` summand of the closed coproduct family is `X'`. -/
theorem closedFamily_false (f : X' ⟶ X) (i : Z ⟶ X) :
    closedFamily f i false = X' :=
  rfl

/-- The `true` summand of the closed coproduct family is `Z`. -/
theorem closedFamily_true (f : X' ⟶ X) (i : Z ⟶ X) :
    closedFamily f i true = Z :=
  rfl

/-- The coproduct `Y = X' ⨿ Z` of the proper source with the closed subspace. -/
def closedCoprod (f : X' ⟶ X) (i : Z ⟶ X) : AlgebraicSpace S :=
  coproduct (closedFamily f i)

/-- The closed coproduct is the sheaf coproduct of `closedFamily`. -/
theorem closedCoprod_eq_coproduct (f : X' ⟶ X) (i : Z ⟶ X) :
    closedCoprod f i = coproduct (closedFamily f i) :=
  rfl

/-- The structure morphism `g : Y ⟶ X` of the closed coproduct. -/
def closedCoprodToAmbient (f : X' ⟶ X) (i : Z ⟶ X) : closedCoprod f i ⟶ X :=
  coproductDesc fun b ↦
    match b with
    | false => (f : closedFamily f i false ⟶ X)
    | true => (i : closedFamily f i true ⟶ X)

/-- The coproduct inclusion of `X'` recovers `f` after composing with
`closedCoprodToAmbient`. -/
theorem coproductι_closedCoprodToAmbient_false (f : X' ⟶ X) (i : Z ⟶ X) :
    coproductι (closedFamily f i) false ≫ closedCoprodToAmbient f i = f :=
  sorry

/-- The coproduct inclusion of `Z` recovers `i` after composing with
`closedCoprodToAmbient`. -/
theorem coproductι_closedCoprodToAmbient_true (f : X' ⟶ X) (i : Z ⟶ X) :
    coproductι (closedFamily f i) true ≫ closedCoprodToAmbient f i = i :=
  sorry

/-- The closed-coproduct structure morphism is proper. -/
instance instProper_closedCoprodToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f] : Proper (closedCoprodToAmbient f i) :=
  sorry

/-- The closed-coproduct structure morphism is surjective when `f` is an
isomorphism over the complementary open of `i`. -/
theorem surjective_closedCoprodToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    Surjective (closedCoprodToAmbient f i) :=
  sorry

/-- The kernel-pair coequalizer `X₁` of `s, t : R ⇉ Y` for `Y = X' ⨿ Z`. -/
abbrev closedSpace (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] : AlgebraicSpace S :=
  KernelPairCoequalizer.space (closedCoprodToAmbient f i)

/-- `closedSpace` is the kernel-pair coequalizer of `closedCoprodToAmbient`. -/
theorem closedSpace_eq (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] :
    closedSpace f i = KernelPairCoequalizer.space (closedCoprodToAmbient f i) :=
  rfl

/-- The structure morphism `X₁ ⟶ X` of the closed coproduct coequalizer. -/
abbrev closedSpaceToAmbient (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] : closedSpace f i ⟶ X :=
  KernelPairCoequalizer.toTarget (closedCoprodToAmbient f i)

/-- The coequalizer projection `Y ⟶ X₁`. -/
abbrev fromClosedCoprod (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] : closedCoprod f i ⟶ closedSpace f i :=
  KernelPairCoequalizer.fromSource (closedCoprodToAmbient f i)

/-- The coequalizer projection lies over `X`. -/
theorem fromClosedCoprod_comp_closedSpaceToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f] :
    fromClosedCoprod f i ≫ closedSpaceToAmbient f i = closedCoprodToAmbient f i :=
  sorry

/-- The lift of the closed immersion `i : Z ⟶ X` through `X₁`. -/
def closedLift (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] : Z ⟶ closedSpace f i :=
  coproductι (closedFamily f i) true ≫ fromClosedCoprod f i

/-- `closedLift` is the `Z`-summand inclusion followed by the coequalizer
projection. -/
theorem closedLift_eq (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] :
    closedLift f i = coproductι (closedFamily f i) true ≫ fromClosedCoprod f i :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
