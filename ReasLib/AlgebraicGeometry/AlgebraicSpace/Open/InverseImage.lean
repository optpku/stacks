/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RepresentableProperties
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Open

variable {S : Scheme.{u}} {X Y V : AlgebraicSpace S}

/-- The inverse-image presheaf of an open subspace satisfies fppf descent. -/
theorem inverseImage_isSheaf (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι) := sorry

/-- The inverse-image presheaf of an open subspace has representable diagonal. -/
theorem inverseImage_representableDiagonal (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    yoneda.relativelyRepresentable
      (diag (pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι)) := sorry

/-- The inverse-image presheaf of an open subspace admits a representable étale,
locally-surjective scheme atlas. -/
theorem inverseImage_atlas (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    ∃ (U : Over S) (chart : yoneda.obj U ⟶
      pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι),
      Representable.Etale chart ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) chart := sorry

/-- The inverse image of an open subspace is the algebraic space whose functor of points is
the presheaf fiber product. -/
def inverseImage (f : X ⟶ Y) (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι) :
    AlgebraicSpace S :=
  ofFunctor (pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι)
    (inverseImage_isSheaf f ι h_open) (inverseImage_representableDiagonal f ι h_open)
    (inverseImage_atlas f ι h_open)

/-- The inclusion of an inverse-image open subspace is the first presheaf pullback
projection. -/
def inverseImageι (f : X ⟶ Y) (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι) :
    inverseImage f ι h_open ⟶ X :=
  pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) f ι

/-- The morphism from an inverse-image open subspace to the given open is the second
presheaf pullback projection. -/
def inverseImageTo (f : X ⟶ Y) (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι) :
    inverseImage f ι h_open ⟶ V :=
  pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) f ι

/-- The inclusion of the inverse image of an open subspace is a representable open
immersion. -/
theorem inverseImage_isOpenImmersion (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    Representable.IsOpenImmersion (inverseImageι f ι h_open) := sorry

/-- The inverse-image space has the presheaf fiber product as its functor of points, and its
two projections form the corresponding presheaf pullback square. -/
theorem inverseImage_spec (f : X ⟶ Y) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) :
    (inverseImage f ι h_open).functorOfPoints =
        pullback (C := (Over S)ᵒᵖ ⥤ Type u) f ι ∧
      IsPullback (C := (Over S)ᵒᵖ ⥤ Type u)
        (inverseImageι f ι h_open) (inverseImageTo f ι h_open) f ι := sorry

end AlgebraicGeometry.AlgebraicSpace.Open
