module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Opposite
public import ReasLib.AlgebraicTopology.DoldKan.QInftyImage
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The canonical degenerate cochain image

This leaf transports the categorical image of the complementary Dold--Kan projector through
opposites. Objectwise image data uses only `HasImages`; the functorial and natural-transformation
layer adds `HasImageMaps`. It is independent of both the degreewise span presentation of degenerate
cochains and the normalized quotient of the resulting image inclusion.

@stack 019I
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [hI : HasImages (ChainComplex Aᵒᵖ ℕ)]

include hI

/-- The canonical degenerate cochain complex of a cosimplicial object. -/
@[stacks 019I "canonical degenerate cochain image"]
abbrev obj (U : CosimplicialObject A) : CochainComplex A ℕ :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).obj
    (Opposite.op (QInfty.image U.op))

/-- The degree-`n` object of the canonical image is the unopposite of the corresponding chain
image object. -/
@[simp, stacks 019I "canonical degenerate cochain image object formula"]
theorem obj_X (U : CosimplicialObject A) (n : ℕ) :
    (obj U).X n = Opposite.unop ((QInfty.image U.op).X n) := sorry

/-- The cochain differential of the canonical image is the unopposite of the chain differential.
-/
@[simp, stacks 019I "canonical degenerate cochain image differential formula"]
theorem obj_d (U : CosimplicialObject A) (n : ℕ) :
    (obj U).d n (n + 1) = ((QInfty.image U.op).d (n + 1) n).unop := sorry

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

/-- The canonical degenerate cochain functor, obtained from the image of `QInfty`. -/
@[stacks 019I "canonical degenerate cochain image functor"]
abbrev functor : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  ((CategoryTheory.cosimplicialSimplicialEquiv A).functor ⋙
      QInfty.imageFunctor (C := Aᵒᵖ)).rightOp ⋙
    HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)

/-- The functorial image object agrees with the assumption-minimal object owner. -/
@[simp, stacks 019I "canonical degenerate cochain image functor object formula"]
theorem functor_obj (U : CosimplicialObject A) :
    (functor (A := A)).obj U = obj U := sorry

end Functorial

namespace opposite

/-- The inclusion of the opposite-simplicial `QInfty` image into the alternating-face model. -/
@[stacks 019I "canonical opposite degenerate cochain inclusion"]
noncomputable def ι (U : CosimplicialObject A) :
    degenerate.obj U ⟶ alternatingCoface.opposite.complex.obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((QInfty.toImage U.op).op)

/-- The projection from the opposite-simplicial alternating-face model to the `QInfty` image. -/
@[stacks 019I "canonical opposite degenerate cochain projection"]
noncomputable def ρ (U : CosimplicialObject A) :
    alternatingCoface.opposite.complex.obj U ⟶ degenerate.obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((QInfty.fromImage U.op).op)

end opposite

/-- The inclusion of the canonical degenerate cochain image into the alternating coface model. -/
@[stacks 019I "canonical degenerate cochain inclusion"]
noncomputable def ι (U : CosimplicialObject A) :
    degenerate.obj U ⟶ (alternatingCofaceMapComplex A).obj U :=
  degenerate.opposite.ι U ≫ (alternatingCoface.opposite.appIso U).inv

/-- The projection from the alternating coface model onto the canonical degenerate cochain image. -/
@[stacks 019I "canonical degenerate cochain projection"]
noncomputable def ρ (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ degenerate.obj U :=
  (alternatingCoface.opposite.appIso U).hom ≫ degenerate.opposite.ρ U

/-- The degreewise component of the canonical degenerate cochain inclusion. -/
@[simp, stacks 019I "canonical degenerate cochain inclusion component"]
theorem ι.f (U : CosimplicialObject A) (n : ℕ) :
    (ι U).f n =
      (degenerate.opposite.ι U).f n ≫ (alternatingCoface.opposite.appIso U).inv.f n := sorry

/-- The degreewise component of the canonical degenerate cochain projection. -/
@[simp, stacks 019I "canonical degenerate cochain projection component"]
theorem ρ.f (U : CosimplicialObject A) (n : ℕ) :
    (ρ U).f n =
      (alternatingCoface.opposite.appIso U).hom.f n ≫
        (degenerate.opposite.ρ U).f n := sorry

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

namespace ι

/-- The canonical degenerate cochain inclusions are natural in the cosimplicial object. -/
@[reassoc, stacks 019I "canonical degenerate cochain inclusion naturality"]
theorem naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    degenerate.functor.map f ≫ ι V = ι U ≫ (alternatingCofaceMapComplex A).map f := sorry

/-- The canonical degenerate cochain inclusions form a natural transformation. -/
@[stacks 019I "canonical degenerate cochain inclusion natural transformation"]
noncomputable def natTrans :
    degenerate.functor ⟶ alternatingCofaceMapComplex A :=
  (Functor.whiskerRight
      (NatTrans.rightOp
        (Functor.whiskerLeft
          (CategoryTheory.cosimplicialSimplicialEquiv A).functor
          (QInfty.toImage.natTrans (C := Aᵒᵖ))))
      (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))) ≫
    (alternatingCoface.opposite.iso (A := A)).inv

/-- The component of the canonical inclusion natural transformation. -/
@[simp, stacks 019I "canonical degenerate cochain inclusion natural transformation component"]
theorem natTrans.app (U : CosimplicialObject A) :
    (natTrans (A := A)).app U = ι U := sorry

end ι

namespace ρ

/-- The canonical degenerate cochain projections are natural in the cosimplicial object. -/
@[reassoc, stacks 019I "canonical degenerate cochain projection naturality"]
theorem naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫ ρ V = ρ U ≫ degenerate.functor.map f := sorry

/-- The canonical degenerate cochain projections form a natural transformation. -/
@[stacks 019I "canonical degenerate cochain projection natural transformation"]
noncomputable def natTrans :
    alternatingCofaceMapComplex A ⟶ degenerate.functor :=
  (alternatingCoface.opposite.iso (A := A)).hom ≫
    Functor.whiskerRight
      (NatTrans.rightOp
        (Functor.whiskerLeft
          (CategoryTheory.cosimplicialSimplicialEquiv A).functor
          (QInfty.fromImage.natTrans (C := Aᵒᵖ))))
      (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))

/-- The component of the canonical projection natural transformation. -/
@[simp, stacks 019I "canonical degenerate cochain projection natural transformation component"]
theorem natTrans.app (U : CosimplicialObject A) :
    (natTrans (A := A)).app U = ρ U := sorry

end ρ

end Functorial

/-- The transported complementary projector on the alternating coface complex. -/
@[stacks 019I "canonical degenerate projector"]
noncomputable def projector (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ (alternatingCofaceMapComplex A).obj U :=
  ρ U ≫ ι U

/-- The transported projector is the composite of the canonical projection and inclusion. -/
@[simp, stacks 019I "canonical degenerate projector composite formula"]
theorem ρ_comp_ι (U : CosimplicialObject A) :
    ρ U ≫ ι U = projector U := sorry

section Functorial

variable [hM : HasImageMaps (ChainComplex Aᵒᵖ ℕ)]

include hM

/-- The transported complementary projector natural transformation. -/
@[stacks 019I "canonical degenerate projector natural transformation"]
noncomputable def projector.natTrans :
    alternatingCofaceMapComplex A ⟶ alternatingCofaceMapComplex A :=
  ρ.natTrans (A := A) ≫ ι.natTrans (A := A)

/-- The transported projector natural transformation is the composite of the canonical projection
and inclusion natural transformations. -/
@[simp, stacks 019I "canonical degenerate natural projector composite formula"]
theorem ρ.natTrans_comp_ι :
    ρ.natTrans (A := A) ≫ ι.natTrans (A := A) = projector.natTrans (A := A) := sorry

/-- The component of the transported complementary projector natural transformation. -/
@[simp, stacks 019I "canonical degenerate projector natural transformation component"]
theorem projector.natTrans.app (U : CosimplicialObject A) :
    (projector.natTrans (A := A)).app U = projector U := sorry

end Functorial

end CategoryTheory.CosimplicialObject.DoldKan.degenerate
