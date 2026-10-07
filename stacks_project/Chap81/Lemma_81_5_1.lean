module

public import stacks_project.Chap74.Definition_74_22_11_Effectivity
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Lemma 81.5.1

A proper surjective morphism of algebraic spaces effectively descends étale
morphisms: an étale descent datum relative to such a morphism is isomorphic
to the canonical descent datum of an étale morphism of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData

/-- Lemma 81.5.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper surjective
morphism of algebraic spaces over `S`. Any descent datum `(U / X, φ)` relative
to `f` with `U` étale over `X` is effective. More precisely, there exists an
étale morphism `V ⟶ Y` of algebraic spaces whose corresponding canonical
descent datum is isomorphic to `(U / X, φ)`. -/
@[stacks 0GG0]
theorem existsEtale_of_proper_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [Proper f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [Etale (D.obj ⟨⟩).hom] :
    ∃ (V : Over Y) (_ : Etale V.hom),
      Nonempty (ofObj (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) V ≅ D) :=
  sorry

/-- A descent datum relative to a proper surjective morphism of algebraic spaces
is effective as soon as its unique component is étale. -/
theorem isEffective_of_etale_of_proper_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [Proper f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [Etale (D.obj ⟨⟩).hom] : D.IsEffective :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DescentData
