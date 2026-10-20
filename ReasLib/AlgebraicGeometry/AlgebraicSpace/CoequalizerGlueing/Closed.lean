module

public import Mathlib.Data.Countable.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen

/-!
# Closed-coproduct kernel-pair coequalizers

For a proper morphism that is an isomorphism over the complement of a closed
immersion, the kernel-pair quotient of the coproduct with the closed subspace
is a finite universal homeomorphism, is unchanged over the complement, and
receives the canonical lift of the closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

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

/-- The closed-coproduct structure morphism is proper. -/
instance instProper_closedCoprodToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f] : Proper (closedCoprodToAmbient f i) :=
  sorry

/-- The closed-coproduct structure morphism is surjective when `f` is an
isomorphism over the complementary open of `i`. -/
instance surjective_closedCoprodToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f]
    [IsIso (openInverseImageTo f (closedImmersionComplementι i))] :
    Surjective (closedCoprodToAmbient f i) :=
  sorry

/-- The kernel-pair coequalizer of the structure morphism of `X' ⨿ Z`. -/
abbrev closedSpace (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] : AlgebraicSpace S :=
  KernelPairCoequalizer.space (closedCoprodToAmbient f i)

/-- The closed-coproduct quotient is the canonical kernel-pair coequalizer. -/
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

/-- The lift of the closed immersion `i : Z ⟶ X` through `X₁`. -/
def closedLift (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] : Z ⟶ closedSpace f i :=
  coproductι (closedFamily f i) true ≫ fromClosedCoprod f i

/-- The closed lift is the `Z`-summand inclusion followed by the coequalizer
projection. -/
theorem closedLift_eq (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] :
    closedLift f i = coproductι (closedFamily f i) true ≫ fromClosedCoprod f i :=
  rfl

/-- The closed-coproduct quotient map to the ambient space is a universal
homeomorphism when `f` is an isomorphism over the complement of `i`. -/
instance universalHomeomorphism_closedSpaceToAmbient (f : X' ⟶ X)
    (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    [IsIso (openInverseImageTo f (closedImmersionComplementι i))] :
    UniversalHomeomorphism (closedSpaceToAmbient f i) :=
  inferInstance

/-- The closed-coproduct quotient map is an isomorphism over the complement
of `i` when `f` is an isomorphism over that complement. -/
instance isIsoOverOpen_closedSpaceToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    [IsIso (openInverseImageTo f (closedImmersionComplementι i))] :
    IsIso (openInverseImageTo (closedSpaceToAmbient f i)
      (closedImmersionComplementι i)) :=
  sorry

/-- The canonical closed lift composes with the quotient structure morphism
to the original closed immersion. -/
theorem closedLift_comp (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] :
    closedLift f i ≫ closedSpaceToAmbient f i = i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
