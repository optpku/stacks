module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
import StacksCheckRecall

/-!
# Fibre dimension at a point of a locally finite-type morphism

For a locally finite-type morphism of algebraic spaces, the relative dimension
at a source point is the sum of the dimension of the local ring of the fibre
and the residue-field transcendence degree, in the notation of
Definition 67.33.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.34.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `x` be a point of `|X|`. If `f` is locally of
finite type, then the relative dimension of `f` at `x` equals the dimension of
the local ring of the fibre of `f` at `x` plus the transcendence degree of
`x / f(x)`, in the notation of Definition 67.33.1. -/
@[stacks 04NQ] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeDimensionAt_eq_fiberStalkDim_add_trdeg :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] {d r : ℕ∞} {x : Points X},
      FiberStalkDimEqAt f d x → ResidueFieldTrdegEqAt f r x →
        RelativeDimensionEqAt f (d + r) x)

/- If `f` has relative dimension `e` at `x`, fibre-stalk dimension `d` at `x`,
and residue-field transcendence degree `r` at `x`, then `e = d + r`. -/
#check (AlgebraicGeometry.AlgebraicSpace.relativeDimensionAt_add_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {d r e : ℕ∞} {x : Points X},
    RelativeDimensionEqAt f e x → FiberStalkDimEqAt f d x →
      ResidueFieldTrdegEqAt f r x → e = d + r)

/- On any étale scheme square over a locally finite-type morphism of algebraic
spaces, the local topological Krull dimension of the scheme-theoretic fibre
equals the Krull dimension of the fibre stalk plus the residue-field
transcendence degree. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleSquare_topologicalKrullDimAt_eq_stalk_add_trdeg :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {U V : Over S} (a : ofOver U ⟶ X)
    (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = ofOverMap h ≫ b →
          topologicalKrullDimAt (h.left.asFiber u) =
            ringKrullDim (Scheme.Hom.fiberStalkAt h.left u) +
              Scheme.Hom.residueFieldTrdegAt h.left u)

end AlgebraicGeometry.AlgebraicSpace
