/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_16_4_Separated
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap110.Lemma_110_75_1_McQuillan
public import stacks_project.Chap87.Lemma_87_9_10_Map
public import stacks_project.Chap87.Lemma_87_5_6_CompletedRing

/-!
# Fibre products of affine formal algebraic spaces over a separated base

Over a separated formal algebraic space `Z`, fibre products of affine (resp.
McQuillan affine) formal algebraic spaces remain affine (resp. McQuillan).
McQuillan affines corresponding to weakly admissible `S`-algebras `A`, `B`,
`C` have fibre product corresponding to `Algebra.TensorProduct.Completed C A B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace IsAffineFormalAlgebraicSpace

/-- Lemma 87.16.4 (1): Let `S` be a scheme. Let `f : X ⟶ Z` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Assume `Z` separated. If `X` and
`Y` are affine formal algebraic spaces, then so is `pullback f g`. -/
@[stacks 0AN3]
instance instPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    [IsSeparatedFormalAlgebraicSpace Z] [HasPullback f g] :
    IsAffineFormalAlgebraicSpace (pullback f g) :=
  sorry

/-- The fibre product object of an `IsPullback` square of morphisms into a
separated formal algebraic space is an affine formal algebraic space when the
two sources are. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Y' Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    [IsSeparatedFormalAlgebraicSpace Z] :
    IsAffineFormalAlgebraicSpace Y' :=
  sorry

end IsAffineFormalAlgebraicSpace

namespace IsMcQuillan

/-- Lemma 87.16.4 (2): Let `S` be a scheme. Let `f : X ⟶ Z` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Assume `Z` separated. If `X` and
`Y` are McQuillan affine formal algebraic spaces, then so is `pullback f g`. -/
@[stacks 0AN3]
instance instPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsMcQuillan X] [IsMcQuillan Y]
    [IsSeparatedFormalAlgebraicSpace Z] [HasPullback f g] :
    IsMcQuillan (pullback f g) :=
  sorry

/-- The fibre product object of an `IsPullback` square of morphisms into a
separated formal algebraic space is McQuillan when the two sources are. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Y' Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    [IsMcQuillan X] [IsMcQuillan Y]
    [IsSeparatedFormalAlgebraicSpace Z] :
    IsMcQuillan Y' :=
  sorry

end IsMcQuillan

namespace AffineFormalAlgebraicSpace

/-- The structure morphism `Spec (Algebra.TensorProduct.Completed C A B) ⟶ S`
induced by a structure morphism of `C`. -/
def completedStructureHom {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra C A] [Algebra C B] [TopologicalSpace A] [TopologicalSpace B]
    {S : Scheme.{u}} (hC : Spec (.of C) ⟶ S) :
    Spec (.of (Algebra.TensorProduct.Completed C A B)) ⟶ S :=
  Spec.map (CommRingCat.ofHom
      (algebraMap C (Algebra.TensorProduct.Completed C A B))) ≫
    hC

/-- `completedStructureHom hC` is `Spec.map` of `algebraMap C (Completed C A B)`
composed with `hC`. -/
theorem completedStructureHom_eq {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra C A] [Algebra C B]
    [TopologicalSpace A] [TopologicalSpace B] {S : Scheme.{u}}
    (hC : Spec (.of C) ⟶ S) :
    completedStructureHom hC =
      Spec.map (CommRingCat.ofHom
          (algebraMap C (Algebra.TensorProduct.Completed C A B))) ≫
        hC :=
  sorry

/-- Lemma 87.16.4 (3): Let `S` be a scheme. Let `X ⟶ Z` and `Y ⟶ Z` be morphisms
of formal algebraic spaces over `S` with `Z` separated. If `X`, `Y`, and `Z` are
McQuillan affine formal algebraic spaces corresponding to weakly admissible
topological `S`-algebras `A`, `B`, and `C`, then the fibre product corresponds
to `Algebra.TensorProduct.Completed C A B`. -/
@[stacks 0AN3]
theorem pullback_spfMap_iso_spfCompleted {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsWeaklyAdmissibleRing C]
    [Algebra C A] [Algebra C B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hφA : Continuous (algebraMap C A)) (hφB : Continuous (algebraMap C B))
    (hA_over : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ hC = hA)
    (hB_over : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ hC = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    [HasPullbacks (Sheaf (Scheme.fppfTopology.over S) (Type u))]
    [TopologicalRing.IsWeaklyAdmissibleRing
      (Algebra.TensorProduct.Completed C A B)] :
    Nonempty
      (pullback (spfMap (algebraMap C A) hφA hA_over)
          (spfMap (algebraMap C B) hφB hB_over) ≅
        spf (Algebra.TensorProduct.Completed C A B)
          (completedStructureHom hC)) :=
  sorry

end AffineFormalAlgebraicSpace

end AlgebraicGeometry

