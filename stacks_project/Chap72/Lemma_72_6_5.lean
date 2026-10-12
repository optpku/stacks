/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap72.Definition_72_6_4_Order

/-!
# Agreement of orders of vanishing on the schematic locus

On a locally Noetherian integral algebraic space, the space-side order of a
rational unit along a prime divisor that meets the schematic locus agrees with
the scheme-side prime-divisor order on a schematic neighbourhood of the generic
point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An open immersion of algebraic spaces preserves dense opens. -/
theorem preservesDenseOpens_of_isOpenImmersion {Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsOpenImmersion f] : PreservesDenseOpens f :=
  sorry

/-- The top open of an integral scheme is nonempty. -/
instance instNonempty_top_opens_of_isIntegral {Y : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Y] : Nonempty (⊤ : Y.Opens) :=
  sorry

namespace PrimeDivisor

/-- A prime divisor meets the schematic locus if and only if its generic point
lies in the schematic locus. -/
theorem meetsSchematicLocus_iff [IsIntegral X] (Z : PrimeDivisor X) :
    (Z.pointsSet ∩ (schematicLocus X).pointsSet).Nonempty ↔
      Z.genericPoint ∈ (schematicLocus X).pointsSet :=
  sorry

/-- The scheme-side unit `f'` is the restriction of `f` along the open immersion
`ι`, compared after `rationalFunctionComap` and the global-sections fraction
map into `RationalFunction (ofOver U)`. -/
def IsRestrictionAlong {U : Over S} (ι : ofOver U ⟶ X) [IsOpenImmersion ι]
    [AlgebraicGeometry.IsIntegral U.left]
    (f : (RationalFunction X)ˣ) (f' : U.left.functionFieldˣ) : Prop :=
  ∃ (a b : Γ(U.left, ⊤)) (hb : b ∈ nonZeroDivisors Γ(U.left, ⊤))
    (hunit : IsUnit (U.left.germToFunctionField ⊤ b)),
    (f' : U.left.functionField) =
        U.left.germToFunctionField ⊤ a * (hunit.unit⁻¹ : U.left.functionField) ∧
      rationalFunctionComap (preservesDenseOpens_of_isOpenImmersion ι)
          (f : RationalFunction X) =
        sectionsFractionsToRationalFunction U
          (IsLocalization.mk' (FractionRing Γ(U.left, ⊤)) a ⟨b, hb⟩)

/-- Unfolding form of `IsRestrictionAlong`. -/
theorem isRestrictionAlong_iff {U : Over S} (ι : ofOver U ⟶ X) [IsOpenImmersion ι]
    [AlgebraicGeometry.IsIntegral U.left]
    (f : (RationalFunction X)ˣ) (f' : U.left.functionFieldˣ) :
    IsRestrictionAlong ι f f' ↔
      ∃ (a b : Γ(U.left, ⊤)) (hb : b ∈ nonZeroDivisors Γ(U.left, ⊤))
        (hunit : IsUnit (U.left.germToFunctionField ⊤ b)),
        (f' : U.left.functionField) =
            U.left.germToFunctionField ⊤ a * (hunit.unit⁻¹ : U.left.functionField) ∧
          rationalFunctionComap (preservesDenseOpens_of_isOpenImmersion ι)
              (f : RationalFunction X) =
            sectionsFractionsToRationalFunction U
              (IsLocalization.mk' (FractionRing Γ(U.left, ⊤)) a ⟨b, hb⟩) :=
  sorry

/-- If the generic point of a prime divisor lies in the schematic locus, then
there is an open immersion from a locally Noetherian integral scheme carrying
the corresponding prime divisor and the restriction of `f`. -/
theorem exists_openImmersion_of_mem_schematicLocus [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (h_meets : Z.genericPoint ∈ (schematicLocus X).pointsSet) :
    ∃ (U : Over S) (ι : ofOver U ⟶ X),
      IsOpenImmersion ι ∧ AlgebraicGeometry.IsLocallyNoetherian U.left ∧
        AlgebraicGeometry.IsIntegral U.left ∧
          ∀ [IsOpenImmersion ι] [AlgebraicGeometry.IsLocallyNoetherian U.left]
            [AlgebraicGeometry.IsIntegral U.left],
            ∃ (Z' : AlgebraicGeometry.PrimeDivisor U.left)
              (f' : U.left.functionFieldˣ),
              Points.mapOfOver ι Z'.genericPoint = Z.genericPoint ∧
                IsRestrictionAlong ι f f' :=
  sorry

/-- Lemma 72.6.5: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `f ∈ (RationalFunction X)ˣ`. If the prime divisor
`Z ⊂ X` meets the schematic locus of `X`, then the order of vanishing `Z.ord f`
of Definition 72.6.4 agrees with the order of vanishing of Divisors,
Definition 31.26.3, recorded as `Scheme.primeDivisorOrder U.left Z' f'` on a
scheme open neighbourhood `ι : ofOver U ⟶ X` of `Z.genericPoint`, where `f'` is
the restriction of `f` along `ι`. -/
@[stacks 0ENM]
theorem ord_eq_primeDivisorOrder [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (h_meets : Z.genericPoint ∈ (schematicLocus X).pointsSet)
    {U : Over S} {ι : ofOver U ⟶ X} [IsOpenImmersion ι]
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsIntegral U.left]
    (Z' : AlgebraicGeometry.PrimeDivisor U.left) (f' : U.left.functionFieldˣ)
    (hξ : Points.mapOfOver ι Z'.genericPoint = Z.genericPoint)
    (hrest : IsRestrictionAlong ι f f') :
    Z.ord f = Scheme.primeDivisorOrder U.left Z' f' :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
