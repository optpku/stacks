module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_3_Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber

/-!
# Fibres of points of algebraic spaces

A pair of morphisms of algebraic spaces determines, at a pair of points of the
targets, the set of points of the common source mapping to both.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

#check (AlgebraicGeometry.AlgebraicSpace.Points.fibre :
  ∀ {S : Scheme.{u}} {W X Z : AlgebraicSpace S},
    (W ⟶ X) → (W ⟶ Z) → Points X → Points Z → Set (Points W))

#check (AlgebraicGeometry.AlgebraicSpace.Points.mem_fibre_iff :
  ∀ {S : Scheme.{u}} {W X Z : AlgebraicSpace S}
    (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z) (w : Points W),
    w ∈ fibre p q x z ↔ map p w = x ∧ map q w = z)

#check (AlgebraicGeometry.AlgebraicSpace.Points.fibre_eq :
  ∀ {S : Scheme.{u}} {W X Z : AlgebraicSpace S}
    (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z),
    fibre p q x z = { w | map p w = x ∧ map q w = z })

#check (AlgebraicGeometry.AlgebraicSpace.Points.fibre_eq_inter :
  ∀ {S : Scheme.{u}} {W X Z : AlgebraicSpace S}
    (p : W ⟶ X) (q : W ⟶ Z) (x : Points X) (z : Points Z),
    fibre p q x z = map p ⁻¹' {x} ∩ map q ⁻¹' {z})

#check (AlgebraicGeometry.AlgebraicSpace.Points.fibre_eq_pullbackComparison_preimage :
  ∀ {S : Scheme.{u}} {W X Z Y : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback p q f g) (x : Points X) (z : Points Z) (hy : map f x = map g z),
    fibre p q x z = pullbackComparison h ⁻¹' {⟨(x, z), hy⟩})

#check (AlgebraicGeometry.AlgebraicSpace.Points.nonempty_fibre_iff :
  ∀ {S : Scheme.{u}} {W X Z Y : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback p q f g) (x : Points X) (z : Points Z),
    (fibre p q x z).Nonempty ↔ map f x = map g z)

end AlgebraicGeometry.AlgebraicSpace.Points
