module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
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

#check (AlgebraicGeometry.AlgebraicSpace.precoverage :
  ∀ {S : Scheme.{u}}, MorphismProperty (AlgebraicSpace S) →
    Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_precoverage_iff :
  ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X : AlgebraicSpace S} {ι : Type v} {Xᵢ : ι → AlgebraicSpace S}
    (f : ∀ i, Xᵢ i ⟶ X),
    Presieve.ofArrows Xᵢ f ∈ precoverage P X ↔
      (∀ i, P (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.etalePrecoverage :
  ∀ {S : Scheme.{u}}, Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_etalePrecoverage_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X),
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X ↔
      (∀ i, Etale (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_etalePrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X)
    (h_etale : ∀ i, Etale (f i))
    (h_cover : (⋃ i, Set.range (Points.map (f i))) = Set.univ),
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X)

#check (AlgebraicGeometry.AlgebraicSpace.EtaleCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}, (ι → Over X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.etaleCovering_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (family : ι → Over X),
    EtaleCovering family ↔
      (∀ i, Etale (family i).hom) ∧
        (⋃ i, Set.range (Points.map (family i).hom)) = Set.univ)

end AlgebraicGeometry.AlgebraicSpace
