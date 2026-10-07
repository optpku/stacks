module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Fppf coverings of algebraic spaces

An fppf covering of an algebraic space is a family of morphisms that are each
flat and locally of finite presentation, and jointly surjective on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points induced by an indexed family of morphisms of algebraic
spaces. -/
def fppfCoveringPointMap {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) :
    (Σ i, Points (Xi i)) → Points X :=
  fun p ↦ Points.map (f p.1) p.2

/-- The point map of an indexed family evaluates by the induced map on points. -/
@[simp]
theorem fppfCoveringPointMap_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X)
    (p : Σ i, Points (Xi i)) :
    fppfCoveringPointMap Xi f p = Points.map (f p.1) p.2 := sorry

/-- An indexed family of morphisms of algebraic spaces over `S` is an fppf
covering when each morphism is flat and locally of finite presentation and the
family is jointly surjective on points. -/
@[mk_iff]
class FppfCovering {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) : Prop where
  /-- Every member of the family is flat. -/
  flat : ∀ i, Flat (f i)
  /-- Every member of the family is locally of finite presentation. -/
  locallyOfFinitePresentation : ∀ i, LocallyOfFinitePresentation (f i)
  /-- The images of the induced maps on points jointly cover the target. -/
  covers : ⋃ i, Set.range (Points.map (f i)) = Set.univ

namespace FppfCovering

/-- The identity family `{𝟙 X}` is an fppf covering. -/
instance instId {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FppfCovering (fun _ : PUnit ↦ X) (fun _ ↦ 𝟙 X) :=
  sorry

/-- Every member of an fppf covering family is flat. -/
instance instFlat {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    [FppfCovering Xi f] (i : ι) : Flat (f i) :=
  ‹FppfCovering Xi f›.flat i

/-- Every member of an fppf covering family is locally of finite presentation. -/
instance instLocallyOfFinitePresentation {S : Scheme.{u}} {ι : Type v}
    {X : AlgebraicSpace S} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    [FppfCovering Xi f] (i : ι) : LocallyOfFinitePresentation (f i) :=
  ‹FppfCovering Xi f›.locallyOfFinitePresentation i

/-- An fppf covering family is flat, locally of finite presentation, and jointly
surjective on points. -/
theorem source_spec {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) [FppfCovering Xi f] :
    (∀ i, Flat (f i)) ∧
      (∀ i, LocallyOfFinitePresentation (f i)) ∧
        ⋃ i, Set.range (Points.map (f i)) = Set.univ := sorry

/-- The point map of an fppf covering family is surjective. -/
theorem surjective_pointMap {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) [FppfCovering Xi f] :
    Function.Surjective (fppfCoveringPointMap Xi f) := sorry

/-- Every point of the target has a preimage under the point map of an fppf
covering family. -/
theorem exists_preimage {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) [FppfCovering Xi f]
    (x : Points X) :
    ∃ p : Σ i, Points (Xi i), fppfCoveringPointMap Xi f p = x := sorry

end FppfCovering

/-- A bundled fppf covering of an algebraic space. -/
structure FppfCover {S : Scheme.{u}} (F : AlgebraicSpace S) where
  /-- The index type of the covering. -/
  I₀ : Type v
  /-- The algebraic spaces in the covering family. -/
  X : I₀ → AlgebraicSpace S
  /-- The covering morphisms. -/
  f : ∀ i, X i ⟶ F
  /-- The family is an fppf covering. -/
  covering : FppfCovering X f

namespace FppfCover

/-- Pack an indexed family together with an fppf covering proof. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X)
    (covering : FppfCovering Xi f) : FppfCover X where
  I₀ := ι
  X := Xi
  f := f
  covering := covering

/-- A bundled fppf covering is flat, locally of finite presentation, and jointly
surjective on points. -/
theorem source_spec {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : FppfCover X) :
    (∀ i, Flat (𝒰.f i)) ∧
      (∀ i, LocallyOfFinitePresentation (𝒰.f i)) ∧
        ⋃ i, Set.range (Points.map (𝒰.f i)) = Set.univ := sorry

/-- The identity covering `{𝟙 X}` as a bundled fppf covering. -/
def id {S : Scheme.{u}} (X : AlgebraicSpace S) : FppfCover X :=
  of (fun _ : PUnit ↦ X) (fun _ ↦ 𝟙 X) inferInstance

end FppfCover

end AlgebraicGeometry.AlgebraicSpace

