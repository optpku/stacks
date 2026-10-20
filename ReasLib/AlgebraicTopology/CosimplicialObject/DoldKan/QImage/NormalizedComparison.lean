module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Quotient
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Normalized
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of normalized quotient models

This leaf identifies the source-facing cokernel of the degreewise degenerate complex with the
cokernel of the canonical `QInfty` image inclusion.  It is independent of the transported Moore
equivalence: only the source/image comparison and the two cokernel universal properties enter.
The objectwise comparison uses strong-epi images for the source/image retract; naturality adds
image maps.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [hZ : HasZeroObject Aᵒᵖ] [hB : HasBinaryCoproducts Aᵒᵖ]
variable [hA : HasImages Aᵒᵖ] [hI : HasImages (ChainComplex Aᵒᵖ ℕ)]
variable [hC : HasCokernels (CochainComplex A ℕ)]

include hZ hB hA hI hC

namespace DoldKan.degenerate.normalized.comparison

variable (U : CosimplicialObject A)

section StrongImage

variable [hE : HasStrongEpiImages (ChainComplex Aᵒᵖ ℕ)]

include hE

/-- The source-facing degenerate inclusion is annihilated by the canonical normalized quotient. -/
@[reassoc (attr := simp), stacks 019I
  "source degenerate inclusion vanishes in the canonical quotient"]
theorem hom_zero :
    degenerateCochainComplex.ι U ≫ DoldKan.degenerate.normalized.π U = 0 := sorry

/-- The canonical image inclusion is annihilated by the source-facing normalized quotient. -/
@[reassoc (attr := simp), stacks 019I
  "canonical degenerate inclusion vanishes in the source quotient"]
theorem inv_zero :
    DoldKan.degenerate.ι U ≫ normalizedCochainComplex.π U = 0 := sorry

/-- The forward normalized-quotient comparison induced by the canonical quotient map. -/
@[stacks 019I "forward normalized cochain quotient comparison"]
noncomputable def hom :
    normalizedCochainComplex U ⟶ DoldKan.degenerate.normalized.obj U :=
  normalizedCochainComplex.desc U
    (DoldKan.degenerate.normalized.π U) (hom_zero U)

/-- The inverse normalized-quotient comparison induced by the source-facing quotient map. -/
@[stacks 019I "inverse normalized cochain quotient comparison"]
noncomputable def inv :
    DoldKan.degenerate.normalized.obj U ⟶ normalizedCochainComplex U :=
  DoldKan.degenerate.normalized.desc U
    (normalizedCochainComplex.π U) (inv_zero U)

/-- Precomposing the forward comparison with the source quotient recovers the canonical quotient
map. -/
@[reassoc, stacks 019I "forward normalized quotient comparison formula"]
theorem π_comp_hom :
    normalizedCochainComplex.π U ≫ hom U =
      DoldKan.degenerate.normalized.π U := sorry

/-- Precomposing the inverse comparison with the canonical quotient recovers the source quotient
map. -/
@[reassoc, stacks 019I "inverse normalized quotient comparison formula"]
theorem π_comp_inv :
    DoldKan.degenerate.normalized.π U ≫ inv U =
      normalizedCochainComplex.π U := sorry

/-- The forward and inverse normalized-quotient comparisons compose to the identity. -/
@[reassoc (attr := simp), stacks 019I "forward-inverse normalized quotient comparison"]
theorem hom_comp_inv : hom U ≫ inv U = 𝟙 _ := sorry

/-- The inverse and forward normalized-quotient comparisons compose to the identity. -/
@[reassoc (attr := simp), stacks 019I "inverse-forward normalized quotient comparison"]
theorem inv_comp_hom : inv U ≫ hom U = 𝟙 _ := sorry

/-- The objectwise comparison is the canonical pair of cokernel descents from their common
alternating-cochain source. -/
@[stacks 019I "normalized cochain comparison with the canonical image quotient"]
noncomputable def iso :
    normalizedCochainComplex U ≅ DoldKan.degenerate.normalized.obj U where
  hom := hom U
  inv := inv U
  hom_inv_id := hom_comp_inv U
  inv_hom_id := inv_comp_hom U

/-- The forward map of the objectwise normalized-quotient isomorphism is the canonical cokernel
descent. -/
@[simp, stacks 019I "forward map of the normalized cochain comparison"]
theorem iso.hom : (iso U).hom = hom U := sorry

/-- The inverse map of the objectwise normalized-quotient isomorphism is the source-facing
cokernel descent. -/
@[simp, stacks 019I "inverse map of the normalized cochain comparison"]
theorem iso.inv : (iso U).inv = inv U := sorry

/-- The comparison identifies the two quotient maps from alternating cochains. -/
@[reassoc (attr := simp), stacks 019I "normalized cochain comparison quotient formula"]
theorem π_comp_iso :
    normalizedCochainComplex.π U ≫ (iso U).hom = DoldKan.degenerate.normalized.π U := sorry

/-- The inverse comparison carries the canonical image quotient map to the source-facing
normalized quotient map. -/
@[reassoc (attr := simp), stacks 019I "canonical image quotient comparison quotient formula"]
theorem π_comp_iso_inv :
    DoldKan.degenerate.normalized.π U ≫ (iso U).inv = normalizedCochainComplex.π U := sorry

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

/-- The forward quotient comparison is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "forward normalized quotient comparison naturality"]
theorem hom.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedCochainComplex.functor.map f ≫ hom V =
      hom U ≫ DoldKan.degenerate.normalized.functor.map f := sorry

/-- The inverse quotient comparison is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "inverse normalized quotient comparison naturality"]
theorem inv.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    DoldKan.degenerate.normalized.functor.map f ≫ inv V =
      inv U ≫ normalizedCochainComplex.functor.map f := sorry

/-- The objectwise normalized-quotient comparisons are natural in the cosimplicial object. -/
@[reassoc, stacks 019I "normalized cochain comparison naturality"]
theorem natIso.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedCochainComplex.functor.map f ≫ (iso V).hom =
      (iso U).hom ≫ DoldKan.degenerate.normalized.functor.map f := sorry

/-- The objectwise normalized-quotient comparisons assemble into a natural isomorphism. -/
@[stacks 019I "normalized cochain comparison natural isomorphism"]
noncomputable def natIso :
    normalizedCochainComplex.functor (A := A) ≅ DoldKan.degenerate.normalized.functor :=
  NatIso.ofComponents (fun U ↦ iso U) (fun f ↦ natIso.naturality f)

/-- The component of the normalized-quotient natural isomorphism is the objectwise comparison. -/
@[simp, stacks 019I "normalized cochain comparison natural isomorphism component"]
theorem natIso.app (U : CosimplicialObject A) :
    (natIso (A := A)).app U = iso U := sorry

/-- The forward component of the natural normalized-quotient comparison is the objectwise
forward comparison. -/
@[simp, stacks 019I "forward component of the normalized cochain comparison"]
theorem natIso.hom_app (U : CosimplicialObject A) :
    (natIso (A := A)).hom.app U = (iso U).hom := sorry

/-- The inverse component of the natural normalized-quotient comparison is the objectwise
inverse comparison. -/
@[simp, stacks 019I "inverse component of the normalized cochain comparison"]
theorem natIso.inv_app (U : CosimplicialObject A) :
    (natIso (A := A)).inv.app U = (iso U).inv := sorry

end Functorial

end StrongImage

end DoldKan.degenerate.normalized.comparison

end CategoryTheory.CosimplicialObject
