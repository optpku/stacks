module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MonObj
open AlgebraicGeometry.Scheme.Hom.Section
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.GroupScheme

/-- The relative identity component of a group scheme, as the fibrewise
connected-component locus of the unit section. -/
noncomputable def identityComponentLocus {S : Scheme.{u}} (G : GroupScheme S) :
    Set G.X.left :=
  componentLocus G.X.hom (η[G.X]).left (Over.w (η[G.X]))

/-- The unit section lands in the relative identity-component locus. -/
theorem one_mem_identityComponentLocus {S : Scheme.{u}} (G : GroupScheme S) (s : S) :
    (η[G.X]).left s ∈ identityComponentLocus G := sorry

/-- Lemma 110.49.1: there exists a group scheme `G` over a base `S` whose identity
component is flat over `S` but which is not flat over `S`. -/
@[stacks 06RK]
theorem exists_identityComponent_flat_not_flat :
    ∃ (S : Scheme.{u}) (G : GroupScheme S) (hopen : IsOpen (identityComponentLocus G)),
      AlgebraicGeometry.Flat
          (Scheme.Opens.ι ⟨identityComponentLocus G, hopen⟩ ≫ G.X.hom) ∧
        ¬ AlgebraicGeometry.Flat G.X.hom := sorry

end AlgebraicGeometry.GroupScheme
