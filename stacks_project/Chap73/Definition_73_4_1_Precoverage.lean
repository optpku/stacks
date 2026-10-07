module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap73.Definition_73_3_1_Precoverage

/-!
# Étale precoverage on algebraic spaces

The étale covering families of algebraic spaces over a scheme `S` are the jointly
surjective families of étale morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The precoverage of jointly surjective `P`-families of morphisms of algebraic
spaces over `S`. -/
def precoverage {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S)) :
    Precoverage (AlgebraicSpace S) :=
  jointlySurjectivePrecoverage S ⊓ MorphismProperty.precoverage P

/-- An indexed family belongs to `precoverage P` if and only if every morphism
satisfies `P` and the images of the induced maps on points cover `|X|`. -/
theorem ofArrows_mem_precoverage_iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ precoverage P X ↔
      (∀ i, P (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

/-- The étale precoverage on algebraic spaces over `S`: jointly surjective families
of étale morphisms. -/
def etalePrecoverage {S : Scheme.{u}} : Precoverage (AlgebraicSpace S) :=
  precoverage (@Etale S)

/-- An indexed family belongs to `etalePrecoverage` if and only if each morphism is
étale and `|X|` equals the union of the images `Points.map (f i)`. -/
theorem ofArrows_mem_etalePrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X ↔
      (∀ i, Etale (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

/-- A family of étale morphisms whose images on points cover `|X|` is an étale
covering family. -/
theorem ofArrows_mem_etalePrecoverage {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X)
    (h_etale : ∀ i, Etale (f i))
    (h_cover : (⋃ i, Set.range (Points.map (f i))) = Set.univ) :
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X :=
  sorry

/-- An indexed family over `X` is an étale covering when its arrows form a covering
presieve for `etalePrecoverage`. -/
abbrev EtaleCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) : Prop :=
  Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
    etalePrecoverage X

/-- An `Over X` family is an étale covering if and only if each arrow is étale and
the images of the induced maps on points cover `|X|`. -/
theorem etaleCovering_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X) :
    EtaleCovering family ↔
      (∀ i, Etale (family i).hom) ∧
        (⋃ i, Set.range (Points.map (family i).hom)) = Set.univ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
