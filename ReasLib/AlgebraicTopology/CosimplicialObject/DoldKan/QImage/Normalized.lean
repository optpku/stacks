/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Degenerate
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical normalized image quotient

This leaf forms the cokernel of the canonical `QInfty` image inclusion and exposes its universal
descent API. Objectwise quotient data uses only chain images and cochain cokernels; functorial
naturality adds image maps. It does not include the separate split-retract consequences of the image
model.

@stack 019I
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [hI : HasImages (ChainComplex Aᵒᵖ ℕ)] [hC : HasCokernels (CochainComplex A ℕ)]

include hI hC

/-- The canonical normalized cochain complex associated to a cosimplicial object. -/
@[stacks 019I "canonical normalized cochain image quotient"]
noncomputable def obj (U : CosimplicialObject A) : CochainComplex A ℕ :=
  cokernel (degenerate.ι U)

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

/-- The canonical normalized cochain functor, defined as the cokernel of the image inclusion. -/
@[stacks 019I "canonical normalized cochain image quotient functor"]
noncomputable def functor : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  (degenerate.ι.natTrans (A := A)).arrowFunctor ⋙ Limits.coker (CochainComplex A ℕ)

/-- The functorial quotient object agrees with the assumption-minimal object owner. -/
@[simp, stacks 019I "canonical normalized cochain functor object formula"]
theorem functor_obj (U : CosimplicialObject A) :
    (functor (A := A)).obj U = obj U := sorry

end Functorial

/-- The quotient map from alternating cochains to the canonical normalized image quotient. -/
@[stacks 019I "canonical normalized cochain image quotient map"]
noncomputable def π (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ obj U :=
  cokernel.π (degenerate.ι U)

/-- The canonical normalized image quotient map is an epimorphism. -/
@[instance, stacks 019I "canonical normalized quotient epimorphism"]
theorem π_epi (U : CosimplicialObject A) : Epi (π U) := sorry

/-- The canonical normalized quotient annihilates the degenerate image. -/
@[reassoc, stacks 019I "canonical normalized quotient annihilates image"]
theorem degenerate_ι_comp_π (U : CosimplicialObject A) :
    degenerate.ι U ≫ π U = 0 := sorry

/-- Descend a cochain map through the canonical normalized image quotient. -/
@[stacks 019I "canonical normalized quotient descent"]
noncomputable def desc (U : CosimplicialObject A) {K : CochainComplex A ℕ}
    (f : (alternatingCofaceMapComplex A).obj U ⟶ K)
    (h : degenerate.ι U ≫ f = 0) : obj U ⟶ K :=
  cokernel.desc (degenerate.ι U) f h

/-- The canonical normalized quotient descent formula. -/
@[reassoc, stacks 019I "canonical normalized quotient descent formula"]
theorem π_desc (U : CosimplicialObject A) {K : CochainComplex A ℕ}
    (f : (alternatingCofaceMapComplex A).obj U ⟶ K)
    (h : degenerate.ι U ≫ f = 0) :
    π U ≫ desc U f h = f := sorry

/-- Morphisms out of the canonical normalized quotient are determined after precomposition. -/
@[ext, stacks 019I "canonical normalized quotient hom extensionality"]
theorem hom_ext (U : CosimplicialObject A) {K : CochainComplex A ℕ}
    {f g : obj U ⟶ K} (h : π U ≫ f = π U ≫ g) : f = g := sorry

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

/-- Naturality of the canonical normalized quotient map. -/
@[reassoc, stacks 019I "canonical normalized quotient naturality"]
theorem π.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫ π V = π U ≫ functor.map f := sorry

/-- The canonical normalized quotient maps form a natural transformation. -/
@[stacks 019I "canonical normalized quotient natural transformation"]
noncomputable def π.natTrans :
    alternatingCofaceMapComplex A ⟶ functor where
  app U := π U
  naturality _ _ f := π.naturality f

/-- The component of the canonical normalized quotient natural transformation. -/
@[simp, stacks 019I "canonical normalized quotient natural transformation component"]
theorem π.natTrans.app (U : CosimplicialObject A) :
    (π.natTrans (A := A)).app U = π U := sorry

end Functorial

section Split

variable [hE : HasStrongEpiImages (ChainComplex Aᵒᵖ ℕ)]

include hE

/-- The complementary projector on alternating cochains. -/
@[stacks 019I "canonical normalized quotient complementary projector"]
noncomputable def complement (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ (alternatingCofaceMapComplex A).obj U :=
  𝟙 _ - degenerate.projector U

/-- The canonical degenerate inclusion is annihilated by the complementary projector. -/
@[reassoc, stacks 019I "canonical normalized quotient complement annihilation"]
theorem degenerate_ι_comp_complement (U : CosimplicialObject A) :
    degenerate.ι U ≫ complement U = 0 := sorry

/-- A section of the canonical normalized quotient, obtained by descending the complement. -/
@[stacks 019I "canonical normalized quotient section"]
noncomputable def ι (U : CosimplicialObject A) :
    obj U ⟶ (alternatingCofaceMapComplex A).obj U :=
  cokernel.desc (degenerate.ι U) (complement U)
    (degenerate_ι_comp_complement U)

/-- The canonical normalized quotient section is a right inverse of the quotient map. -/
@[reassoc, stacks 019I "canonical normalized quotient section quotient identity"]
theorem ι_comp_π (U : CosimplicialObject A) :
    ι U ≫ π U = 𝟙 (obj (A := A) U) := sorry

/-- The quotient followed by its canonical section is the complementary projector. -/
@[reassoc, stacks 019I "canonical normalized quotient projector formula"]
theorem π_comp_ι (U : CosimplicialObject A) :
    π U ≫ ι U = complement U := sorry

namespace ι

/-- A canonical normalized quotient section with its quotient retraction. -/
@[stacks 019I "canonical normalized quotient component split monomorphism"]
noncomputable def appSplitMono (U : CosimplicialObject A) : SplitMono (ι U) where
  retraction := π U
  id := ι_comp_π U

/-- Every canonical normalized quotient section is split monic. -/
@[instance, stacks 019I "canonical normalized quotient component split monomorphism instance"]
theorem appIsSplitMono (U : CosimplicialObject A) : IsSplitMono (ι U) := sorry

end ι

namespace π

/-- A canonical normalized quotient with its complementary section. -/
@[stacks 019I "canonical normalized quotient component split epimorphism"]
noncomputable def appSplitEpi (U : CosimplicialObject A) : SplitEpi (π U) where
  section_ := ι U
  id := ι_comp_π U

/-- Every canonical normalized quotient is split epic. -/
@[instance, stacks 019I "canonical normalized quotient component split epimorphism instance"]
theorem appIsSplitEpi (U : CosimplicialObject A) : IsSplitEpi (π U) := sorry

end π

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

/-- The canonical normalized quotient section is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "canonical normalized quotient section naturality"]
theorem ι.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    functor.map f ≫ ι V = ι U ≫ (alternatingCofaceMapComplex A).map f := sorry

/-- The canonical normalized quotient sections form a natural transformation. -/
@[stacks 019I "canonical normalized quotient section natural transformation"]
noncomputable def ι.natTrans :
    functor (A := A) ⟶ alternatingCofaceMapComplex A where
  app U := ι U
  naturality _ _ f := ι.naturality f

/-- The component of the canonical normalized quotient section transformation. -/
@[simp, stacks 019I "canonical normalized quotient section transformation component"]
theorem ι.natTrans.app (U : CosimplicialObject A) :
    (ι.natTrans (A := A)).app U = ι U := sorry

/-- The canonical normalized quotient section and quotient form a natural retract. -/
@[reassoc, stacks 019I "canonical normalized quotient natural retract law"]
theorem ι.natTrans_comp_π :
    ι.natTrans (A := A) ≫ π.natTrans (A := A) = 𝟙 (functor (A := A)) := sorry

namespace ι

/-- The natural canonical normalized quotient section with its retraction. -/
@[stacks 019I "canonical normalized quotient natural split monomorphism"]
noncomputable def splitMono : SplitMono (ι.natTrans (A := A)) where
  retraction := π.natTrans (A := A)
  id := ι.natTrans_comp_π (A := A)

/-- The natural canonical normalized quotient section is split monic. -/
@[instance, stacks 019I "canonical normalized quotient natural split monomorphism instance"]
theorem isSplitMono : IsSplitMono (ι.natTrans (A := A)) := sorry

end ι

namespace π

/-- The natural canonical normalized quotient with its section. -/
@[stacks 019I "canonical normalized quotient natural split epimorphism"]
noncomputable def splitEpi : SplitEpi (π.natTrans (A := A)) where
  section_ := ι.natTrans (A := A)
  id := ι.natTrans_comp_π (A := A)

/-- The natural canonical normalized quotient is split epic. -/
@[instance, stacks 019I "canonical normalized quotient natural split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (π.natTrans (A := A)) := sorry

end π

/-- The canonical normalized image functor factors through its section and quotient. -/
@[reassoc, stacks 019I "canonical normalized quotient map factorization"]
theorem map_eq_factorization {U V : CosimplicialObject A} (f : U ⟶ V) :
    functor.map f =
      ι U ≫ (alternatingCofaceMapComplex A).map f ≫ π V := sorry

end Functorial

end Split

end CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized
