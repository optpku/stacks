module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.Topology.Stratification.Indexed

/-!
# Stratifications of schemes

A scheme stratification retains the scheme structure of each locally closed stratum together
with its immersion into the ambient scheme. Its underlying image subsets form an indexed
topological stratification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A stratification of a scheme by an ordered family of immersed schemes whose images form a
topological stratification. -/
structure Stratification (S : Scheme.{u}) where
  /-- The type indexing the strata. -/
  index : Type u
  /-- The partial order controlling the frontier relation between strata. -/
  indexOrder : PartialOrder index
  /-- The scheme carried by each stratum. -/
  stratum : index → Scheme.{u}
  /-- The immersion of each stratum into the ambient scheme. -/
  ι : (i : index) → stratum i ⟶ S
  /-- Each stratum map is an immersion. -/
  isImmersion : ∀ i, IsImmersion (ι i)
  /-- The images of the stratum maps form an indexed topological stratification. -/
  isStratification :
    @IsStratification S _ index indexOrder (fun i ↦ Set.range (ι i).base)

namespace Stratification

/-- Construct a scheme stratification from an ordered family of immersed schemes whose images
form a topological stratification. -/
def of {S : Scheme.{u}} (I : Type u) (order : PartialOrder I)
    (stratum : I → Scheme.{u}) (ι : (i : I) → stratum i ⟶ S)
    (isImmersion : ∀ i, IsImmersion (ι i))
    (isStratification :
      @IsStratification S _ I order (fun i ↦ Set.range (ι i).base)) :
    Stratification S where
  index := I
  indexOrder := order
  stratum := stratum
  ι := ι
  isImmersion := isImmersion
  isStratification := isStratification

/-- The morphism from the coproduct of the strata to the ambient scheme. -/
noncomputable def hom {S : Scheme.{u}} (Z : Stratification S) :
    (∐ fun i ↦ Z.stratum i) ⟶ S :=
  Sigma.desc Z.ι

/-- A scheme stratification consists of immersed strata whose images form an indexed
topological stratification. -/
theorem spec {S : Scheme.{u}} (Z : Stratification S) :
    (∀ i, IsImmersion (Z.ι i)) ∧
      @IsStratification S _ Z.index Z.indexOrder
        (fun i ↦ Set.range (Z.ι i).base) := sorry

end Stratification

namespace Hom

/-- A scheme morphism associated to a stratification is a monomorphism which, up to an
isomorphism of its source, is the coproduct morphism of an explicit scheme stratification. -/
class IsStratification {S' S : Scheme.{u}} (p : S' ⟶ S) : Prop extends Mono p where
  /-- A presentation of the morphism by the coproduct of the strata. -/
  exists_presentation :
    ∃ (Z : Scheme.Stratification S) (e : S' ≅ ∐ fun i ↦ Z.stratum i),
      e.hom ≫ Z.hom = p

namespace IsStratification

/-- A stratification morphism is a monomorphism admitting a coproduct presentation by the
immersed schemes of a stratification. -/
theorem spec {S' S : Scheme.{u}} (p : S' ⟶ S) [IsStratification p] :
    Mono p ∧
      ∃ (Z : Scheme.Stratification S) (e : S' ≅ ∐ fun i ↦ Z.stratum i),
        e.hom ≫ Z.hom = p := sorry

end IsStratification

end Hom

end AlgebraicGeometry.Scheme
