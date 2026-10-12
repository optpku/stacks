/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Degenerate
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Degenerate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of the source and projector-image degenerate complexes

This is the assumption-layer bridge between the source-facing degreewise degenerate complex and
the canonical image of the complementary Dold--Kan projector.  Objectwise maps use only the
image data needed by the two constructions; retract laws add strong-epi images, and naturality
adds image maps.  The decomposition leaves consume this bridge but do not own it.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [hZ : HasZeroObject Aᵒᵖ] [hB : HasBinaryCoproducts Aᵒᵖ]
variable [hA : HasImages Aᵒᵖ] [hI : HasImages (ChainComplex Aᵒᵖ ℕ)]

include hZ hB hA hI

namespace DoldKan.degenerate.comparison

variable {U V : CosimplicialObject A}

/-- The comparison from the source-facing degenerate complex to Dold--Kan's image object. -/
@[stacks 019I "source-facing to canonical degenerate comparison"]
def hom (U : CosimplicialObject A) :
    degenerateCochainComplex U ⟶ DoldKan.degenerate.obj U :=
  degenerateCochainComplex.ι U ≫ DoldKan.degenerate.ρ U

/-- The inverse comparison from Dold--Kan's image object to the source-facing complex. -/
@[stacks 019I "canonical to source-facing degenerate comparison"]
def inv (U : CosimplicialObject A) :
    DoldKan.degenerate.obj U ⟶ degenerateCochainComplex U :=
  DoldKan.degenerate.ι U ≫ degenerateCochainComplex.ρ U

section StrongImage

variable [hE : HasStrongEpiImages (ChainComplex Aᵒᵖ ℕ)]

include hE

/-- The forward and inverse degenerate comparisons compose to the identity. -/
@[reassoc (attr := simp), stacks 019I "degenerate comparison forward-inverse law"]
theorem hom_inv_id (U : CosimplicialObject A) : hom U ≫ inv U = 𝟙 _ := sorry

/-- The inverse and forward degenerate comparisons compose to the identity. -/
@[reassoc (attr := simp), stacks 019I "degenerate comparison inverse-forward law"]
theorem inv_hom_id (U : CosimplicialObject A) : inv U ≫ hom U = 𝟙 _ := sorry

/-- The source-facing and canonical degenerate complexes are isomorphic. -/
@[stacks 019I "source-facing canonical degenerate comparison"]
def iso (U : CosimplicialObject A) :
    degenerateCochainComplex U ≅ DoldKan.degenerate.obj U where
  hom := hom U
  inv := inv U
  hom_inv_id := hom_inv_id U
  inv_hom_id := inv_hom_id U

/-- The comparison isomorphism's forward map is `hom`. -/
@[simp, stacks 019I "forward map of the degenerate comparison"]
theorem iso.hom (U : CosimplicialObject A) : (iso U).hom = hom U := sorry

/-- The comparison isomorphism's inverse map is `inv`. -/
@[simp, stacks 019I "inverse map of the degenerate comparison"]
theorem iso.inv (U : CosimplicialObject A) : (iso U).inv = inv U := sorry

/-- The forward comparison intertwines the two degenerate inclusions. -/
@[reassoc (attr := simp), stacks 019I "forward degenerate comparison inclusion formula"]
theorem hom_comp_ι (U : CosimplicialObject A) :
    hom U ≫ DoldKan.degenerate.ι U = degenerateCochainComplex.ι U := sorry

/-- The inverse comparison intertwines the two degenerate inclusions. -/
@[reassoc (attr := simp), stacks 019I "inverse degenerate comparison inclusion formula"]
theorem inv_comp_ι (U : CosimplicialObject A) :
    inv U ≫ degenerateCochainComplex.ι U = DoldKan.degenerate.ι U := sorry

/-- The forward comparison intertwines the two degenerate projections. -/
@[reassoc, stacks 019I "forward degenerate comparison projection formula"]
theorem ρ_comp_hom (U : CosimplicialObject A) :
    degenerateCochainComplex.ρ U ≫ hom U = DoldKan.degenerate.ρ U := sorry

/-- The inverse comparison intertwines the two degenerate projections. -/
@[reassoc, stacks 019I "inverse degenerate comparison projection formula"]
theorem ρ_comp_inv (U : CosimplicialObject A) :
    DoldKan.degenerate.ρ U ≫ inv U = degenerateCochainComplex.ρ U := sorry

end StrongImage

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

namespace hom

/-- The forward comparison is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "forward degenerate comparison naturality"]
theorem naturality (f : U ⟶ V) :
    (degenerateCochainComplex.functor (A := A)).map f ≫ hom V =
      hom U ≫ (DoldKan.degenerate.functor (A := A)).map f := sorry

end hom

namespace inv

/-- The inverse comparison is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "inverse degenerate comparison naturality"]
theorem naturality (f : U ⟶ V) :
    (DoldKan.degenerate.functor (A := A)).map f ≫ inv V =
      inv U ≫ (degenerateCochainComplex.functor (A := A)).map f := sorry

end inv

end Functorial

section NaturalIso

variable [hE : HasStrongEpiImages (ChainComplex Aᵒᵖ ℕ)]
variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hE hM

/-- The pointwise comparison assembles into a natural isomorphism. -/
@[stacks 019I "source-facing canonical degenerate natural isomorphism"]
def natIso : degenerateCochainComplex.functor (A := A) ≅ DoldKan.degenerate.functor :=
  NatIso.ofComponents (fun U ↦ iso U) (fun f ↦ hom.naturality f)

/-- The natural isomorphism's component at an object is `iso`. -/
@[simp, stacks 019I "degenerate comparison natural isomorphism component"]
theorem natIso.app (U : CosimplicialObject A) :
    (natIso (A := A)).app U = iso U := sorry

/-- The forward component of the natural comparison is `hom`. -/
@[simp, stacks 019I "forward component of the degenerate comparison"]
theorem natIso.hom_app (U : CosimplicialObject A) :
    (natIso (A := A)).hom.app U = hom U := sorry

/-- The inverse component of the natural comparison is `inv`. -/
@[simp, stacks 019I "inverse component of the degenerate comparison"]
theorem natIso.inv_app (U : CosimplicialObject A) :
    (natIso (A := A)).inv.app U = inv U := sorry

end NaturalIso

end DoldKan.degenerate.comparison

end CategoryTheory.CosimplicialObject
