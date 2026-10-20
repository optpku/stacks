/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Projection
public import ReasLib.AlgebraicTopology.DoldKan.QInftyImage.Evaluation
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with the canonical `QInfty` image

This leaf identifies the source-facing degreewise degenerate complex with the canonical image
factorization of `QInfty`, including objectwise and functorial comparison isomorphisms.

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan.QInfty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasZeroObject C] [HasBinaryCoproducts C] [HasImages C]

/-- The canonical degreewise image subobject agrees with the source-facing degenerate subobject.
This is the comparison theorem used by textbook-facing bridges. -/
@[stacks 019A "canonical degenerate projector degreewise subobject bridge"]
theorem degreeSubobject_eq (U : SimplicialObject C) (n : ℕ) :
    QInfty.degreeSubobject U n = degenerateSubobject U n := sorry

namespace imageComparison

/-- The degreewise image-subobject carrier is the corresponding object of the source-facing
degenerate complex. This bridge does not require images of whole chain complexes. -/
@[stacks 019A "degree object of the projector-image comparison"]
theorem degreeObject_eq (U : SimplicialObject C) (n : ℕ) :
    (QInfty.degreeSubobject U n : C) = D[U].X n := sorry

end imageComparison

section ChainImage

variable [HasImages (ChainComplex C ℕ)]

namespace imageComparison

/-- The canonical comparison from the image of `QInfty` to the source-facing degenerate complex. -/
@[stacks 019A "canonical projector image to degenerate-complex comparison"]
noncomputable def hom (U : SimplicialObject C) : QInfty.image U ⟶ D[U] :=
  QInfty.fromImage U ≫ degenerateComplex.π U

/-- The canonical comparison from the source-facing degenerate complex to the image of `QInfty`. -/
@[stacks 019A "degenerate complex to canonical projector image comparison"]
noncomputable def inv (U : SimplicialObject C) : D[U] ⟶ QInfty.image U :=
  degenerateComplex.ι U ≫ QInfty.toImage U

/-- The degree-`n` component of the forward comparison is the image inclusion followed by the
source-facing degenerate projection. -/
@[simp, stacks 019A "projector image comparison degree component"]
theorem hom_f (U : SimplicialObject C) (n : ℕ) :
    (hom U).f n = (QInfty.fromImage U).f n ≫ (degenerateComplex.π U).f n := sorry

/-- The degree-`n` component of the inverse comparison is the source-facing degenerate inclusion
followed by the image projection. -/
@[simp, stacks 019A "inverse projector image comparison degree component"]
theorem inv_f (U : SimplicialObject C) (n : ℕ) :
    (inv U).f n = (degenerateComplex.ι U).f n ≫ (QInfty.toImage U).f n := sorry

section StrongImage

variable [HasStrongEpiImages (ChainComplex C ℕ)]

/-- The forward comparison followed by the inverse comparison is the identity on the canonical
image of `QInfty`. -/
@[stacks 019A "projector image comparison forward-inverse law"]
theorem hom_comp_inv (U : SimplicialObject C) :
    hom U ≫ inv U = 𝟙 (QInfty.image U) := sorry

/-- The inverse comparison followed by the forward comparison is the identity on the
source-facing degenerate complex. -/
@[stacks 019A "projector image comparison inverse-forward law"]
theorem inv_comp_hom (U : SimplicialObject C) :
    inv U ≫ hom U = 𝟙 D[U] := sorry

/-- The canonical image of `QInfty` and the source-facing degenerate complex are canonically
isomorphic. -/
@[stacks 019A "canonical projector image and degenerate-complex isomorphism"]
noncomputable def iso (U : SimplicialObject C) : QInfty.image U ≅ D[U] where
  hom := hom U
  inv := inv U
  hom_inv_id := hom_comp_inv U
  inv_hom_id := inv_comp_hom U

/-- The forward map of the objectwise comparison is the canonical comparison morphism. -/
@[simp, stacks 019A "forward map of the projector image comparison"]
theorem iso_hom (U : SimplicialObject C) : (iso U).hom = hom U := sorry

/-- The inverse map of the objectwise comparison is the canonical inverse comparison morphism. -/
@[simp, stacks 019A "inverse map of the projector image comparison"]
theorem iso_inv (U : SimplicialObject C) : (iso U).inv = inv U := sorry

/-- Evaluation of the chain-level projector-image comparison. -/
@[stacks 019A "evaluation of the projector-image comparison"]
noncomputable def evalIso (U : SimplicialObject C) (n : ℕ) :
    (QInfty.image U).X n ≅ D[U].X n :=
  (HomologicalComplex.eval C (ComplexShape.down ℕ) n).mapIso (iso U)

/-- The forward map of `evalIso` is the degree component of the chain-level comparison. -/
@[simp, stacks 019A "forward evaluation of the projector-image comparison"]
theorem evalIso.hom (U : SimplicialObject C) (n : ℕ) :
    (evalIso U n).hom = (iso U).hom.f n := sorry

/-- The inverse map of `evalIso` is the degree component of the inverse chain-level comparison. -/
@[simp, stacks 019A "inverse evaluation of the projector-image comparison"]
theorem evalIso.inv (U : SimplicialObject C) (n : ℕ) :
    (evalIso U n).inv = (iso U).inv.f n := sorry

/-- The forward comparison followed by the source-facing inclusion is the canonical image inclusion. -/
@[reassoc, stacks 019A "projector image comparison inclusion formula"]
theorem hom_comp_ι (U : SimplicialObject C) :
    hom U ≫ degenerateComplex.ι U = QInfty.fromImage U := sorry

/-- Projection to the canonical image followed by the forward comparison is the source-facing
degenerate projection. -/
@[reassoc, stacks 019A "projector image comparison projection formula"]
theorem toImage_comp_hom (U : SimplicialObject C) :
    QInfty.toImage U ≫ hom U = degenerateComplex.π U := sorry

/-- The inverse comparison followed by the canonical image inclusion is the source-facing
degenerate inclusion. -/
@[reassoc, stacks 019A "inverse projector image comparison inclusion formula"]
theorem inv_comp_fromImage (U : SimplicialObject C) :
    inv U ≫ QInfty.fromImage U = degenerateComplex.ι U := sorry

/-- The source-facing degenerate projection followed by the inverse comparison is the canonical
image projection. -/
@[reassoc, stacks 019A "inverse projector image comparison projection formula"]
theorem projection_comp_inv (U : SimplicialObject C) :
    degenerateComplex.π U ≫ inv U = QInfty.toImage U := sorry

end StrongImage

section Functorial

variable [HasImageMaps (ChainComplex C ℕ)]

/-- The forward image-to-degenerate comparison is natural in the simplicial object. -/
@[stacks 019A "naturality of the projector image comparison"]
theorem hom_naturality {U V : SimplicialObject C} (f : U ⟶ V) :
    (QInfty.imageFunctor (C := C)).map f ≫ hom V =
      hom U ≫ degenerateComplex.map f := sorry

/-- The inverse degenerate-to-image comparison is natural in the simplicial object. -/
@[stacks 019A "naturality of the inverse projector image comparison"]
theorem inv_naturality {U V : SimplicialObject C} (f : U ⟶ V) :
    degenerateComplex.map f ≫ inv V =
      inv U ≫ (QInfty.imageFunctor (C := C)).map f := sorry

/-- The canonical image-to-degenerate comparisons form a natural transformation. -/
@[stacks 019A "canonical projector image comparison natural transformation"]
noncomputable def natTrans : QInfty.imageFunctor (C := C) ⟶ degenerateComplex.functor (C := C) where
  app U := hom U
  naturality _ _ f := hom_naturality f

/-- The component of the canonical image-to-degenerate natural transformation is the pointwise
forward comparison. -/
@[simp, stacks 019A "canonical projector image comparison natural component"]
theorem natTrans.app (U : SimplicialObject C) :
    (natTrans (C := C)).app U = hom U := sorry

/-- The canonical degenerate-to-image comparisons form the inverse natural transformation. -/
@[stacks 019A "inverse projector image comparison natural transformation"]
noncomputable def natInv : degenerateComplex.functor (C := C) ⟶ QInfty.imageFunctor (C := C) where
  app U := inv U
  naturality _ _ f := inv_naturality f

/-- The component of the inverse natural transformation is the pointwise inverse comparison. -/
@[simp, stacks 019A "canonical projector image comparison natural component"]
theorem natInv.app (U : SimplicialObject C) :
    (natInv (C := C)).app U = inv U := sorry

end Functorial

section StrongImage

variable [HasStrongEpiImages (ChainComplex C ℕ)]

/-- The forward comparison natural transformation followed by its inverse is the identity. -/
@[stacks 019A "projector image comparison natural forward-inverse law"]
theorem natIso.hom_inv_id :
    natTrans (C := C) ≫ natInv (C := C) = 𝟙 (QInfty.imageFunctor (C := C)) := sorry

/-- The inverse comparison natural transformation followed by the forward comparison is the
identity. -/
@[stacks 019A "projector image comparison natural inverse-forward law"]
theorem natIso.inv_hom_id :
    natInv (C := C) ≫ natTrans (C := C) = 𝟙 (degenerateComplex.functor (C := C)) := sorry

/-- The canonical projector-image functor is naturally isomorphic to the source-facing
degenerate-complex functor. -/
@[stacks 019A "canonical projector image and degenerate-complex natural isomorphism"]
noncomputable def natIso : QInfty.imageFunctor (C := C) ≅ degenerateComplex.functor (C := C) where
  hom := natTrans
  inv := natInv
  hom_inv_id := natIso.hom_inv_id
  inv_hom_id := natIso.inv_hom_id

/-- The component of the natural comparison is the objectwise projector-image comparison. -/
@[simp, stacks 019A "component of the projector image natural isomorphism"]
theorem natIso.app (U : SimplicialObject C) :
    (natIso (C := C)).app U = iso U := sorry

end StrongImage

end imageComparison

end ChainImage

end AlgebraicTopology.DoldKan.QInfty

namespace AlgebraicTopology.DoldKan.QInfty.imageComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasImages (ChainComplex C ℕ)] [HasStrongEpiImages (ChainComplex C ℕ)]

/-- The evaluated chain-level comparison is the canonical degreewise image comparison followed
by the carrier identification with the source-facing degenerate complex. -/
@[stacks 019A "coherence of chain and degree projector-image comparisons"]
theorem evalIso.eq_degreeIso (U : SimplicialObject C) (n : ℕ) :
    evalIso U n = QInfty.degreeIso U n ≪≫ eqToIso (degreeObject_eq U n) := sorry

end AlgebraicTopology.DoldKan.QInfty.imageComparison
