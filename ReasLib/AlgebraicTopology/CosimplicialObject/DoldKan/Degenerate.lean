/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Opposite
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Projection
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Degenerate cochain complexes of cosimplicial objects

The degenerate cochain complex is obtained by applying the simplicial degenerate-complex
construction in the opposite category.  This leaf owns the functor and its canonical inclusion
into the alternating coface complex.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [HasZeroObject Aᵒᵖ] [HasBinaryCoproducts Aᵒᵖ] [HasImages Aᵒᵖ]

/-- The functor assigning the transported degenerate cochain complex to a cosimplicial object. -/
@[stacks 019I "degenerate cochain complex functor"]
abbrev degenerateCochainComplex.functor : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  ((CategoryTheory.cosimplicialSimplicialEquiv A).functor ⋙
      AlgebraicTopology.DoldKan.degenerateComplex.functor).rightOp ⋙
    HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)

/-- The degenerate cochain complex of a cosimplicial object. -/
@[stacks 019I "degenerate cochain complex"]
abbrev degenerateCochainComplex (U : CosimplicialObject A) : CochainComplex A ℕ :=
  degenerateCochainComplex.functor.obj U

namespace degenerateCochainComplex

namespace opposite

/-- The canonical inclusion into the opposite-simplicial model of the alternating coface
complex. -/
@[stacks 019I "degenerate cochain inclusion in the opposite model"]
def ι (U : CosimplicialObject A) :
    degenerateCochainComplex U ⟶ DoldKan.alternatingCoface.opposite.complex.obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((degenerateComplex.π U.op).op)

/-- The canonical projection from the opposite-simplicial model of the alternating coface
complex onto degenerate cochains. -/
@[stacks 019I "degenerate cochain projection in the opposite model"]
def ρ (U : CosimplicialObject A) :
    DoldKan.alternatingCoface.opposite.complex.obj U ⟶ degenerateCochainComplex U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((degenerateComplex.ι U.op).op)

end opposite

/-- The degree-`n` object is the unopposite of the degree-`n` degenerate subobject of `U.op`. -/
@[simp, stacks 019I "degenerate cochain complex object formula"]
theorem obj_X (U : CosimplicialObject A) (n : ℕ) :
    (degenerateCochainComplex U).X n =
      Opposite.unop (degenerateSubobject U.op n : Aᵒᵖ) := sorry

/-- The differential from degree `n` to degree `n + 1` is the unopposite degenerate
differential. -/
@[stacks 019I "degenerate cochain complex differential formula"]
theorem obj_d (U : CosimplicialObject A) (n : ℕ) :
    (degenerateCochainComplex U).d n (n + 1) =
      (degenerateComplex.d U.op n).unop := sorry

/-- The canonical inclusion of the degenerate cochain complex into the alternating coface
complex. -/
@[stacks 019I "degenerate cochain inclusion"]
def ι (U : CosimplicialObject A) :
    degenerateCochainComplex U ⟶ (alternatingCofaceMapComplex A).obj U :=
  opposite.ι U ≫ (DoldKan.alternatingCoface.opposite.appIso U).inv

/-- The degree-`n` component of the degenerate cochain inclusion is the unopposite simplicial
degenerate projection. -/
@[simp, stacks 019I "degenerate cochain inclusion component"]
theorem ι.f (U : CosimplicialObject A) (n : ℕ) :
    (ι U).f n = ((degenerateComplex.π U.op).f n).unop := sorry

/-- Naturality of the inclusion of degenerate cochain complexes. -/
@[reassoc, stacks 019I "degenerate cochain inclusion naturality"]
theorem ι.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    degenerateCochainComplex.functor.map f ≫ ι V =
      ι U ≫ (alternatingCofaceMapComplex A).map f := sorry

/-- The canonical inclusions of degenerate cochain complexes form a natural transformation
`D ⟶ s`. -/
@[stacks 019I "degenerate subcomplex inclusion"]
def ι.natTrans : degenerateCochainComplex.functor ⟶ alternatingCofaceMapComplex A where
  app U := ι U
  naturality _ _ f := ι.naturality f

/-- The inclusion natural transformation has component `ι U` at `U`. -/
@[simp, stacks 019I "degenerate cochain inclusion natural transformation component"]
theorem ι.natTrans.app (U : CosimplicialObject A) :
    (ι.natTrans (A := A)).app U = ι U := sorry

/-- The canonical projection from the alternating coface complex onto degenerate cochains. -/
@[stacks 019I "degenerate cochain projection"]
def ρ (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ degenerateCochainComplex U :=
  (DoldKan.alternatingCoface.opposite.appIso U).hom ≫ opposite.ρ U

/-- The degree-`n` component of the degenerate cochain projection is the unopposite simplicial
degenerate inclusion. -/
@[simp, stacks 019I "degenerate cochain projection component"]
theorem ρ.f (U : CosimplicialObject A) (n : ℕ) :
    (ρ U).f n = ((degenerateComplex.ι U.op).f n).unop := sorry

/-- Naturality of the canonical projection onto degenerate cochains. -/
@[reassoc, stacks 019I "degenerate cochain projection naturality"]
theorem ρ.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫ ρ V =
      ρ U ≫ degenerateCochainComplex.functor.map f := sorry

/-- The canonical projections onto degenerate cochains form a natural transformation `s ⟶ D`. -/
@[stacks 019I "degenerate cochain projection natural transformation"]
def ρ.natTrans : alternatingCofaceMapComplex A ⟶ degenerateCochainComplex.functor where
  app U := ρ U
  naturality _ _ f := ρ.naturality f

/-- The projection natural transformation has component `ρ U` at `U`. -/
@[simp, stacks 019I "degenerate cochain projection natural transformation component"]
theorem ρ.natTrans.app (U : CosimplicialObject A) :
    (ρ.natTrans (A := A)).app U = ρ U := sorry

/-- The degenerate cochain inclusion is a section of the degenerate projection. -/
@[reassoc, stacks 019I "degenerate cochain inclusion-projection retraction"]
theorem ι_comp_ρ (U : CosimplicialObject A) :
    ι U ≫ ρ U = 𝟙 (degenerateCochainComplex U) := sorry

/-- A source-facing degenerate inclusion component, equipped with its canonical retraction. -/
@[stacks 019I "degenerate cochain component split monomorphism"]
def ι.appSplitMono (U : CosimplicialObject A) : SplitMono (ι U) where
  retraction := ρ U
  id := ι_comp_ρ U

/-- Every source-facing degenerate inclusion component is canonically split. -/
@[instance, stacks 019I "degenerate cochain component split monomorphism instance"]
theorem ι.appIsSplitMono (U : CosimplicialObject A) : IsSplitMono (ι U) := sorry

/-- A source-facing degenerate projection component, equipped with its canonical section. -/
@[stacks 019I "degenerate cochain component split epimorphism"]
def ρ.appSplitEpi (U : CosimplicialObject A) : SplitEpi (ρ U) where
  section_ := ι U
  id := ι_comp_ρ U

/-- Every source-facing degenerate projection component is canonically split. -/
@[instance, stacks 019I "degenerate cochain component split epimorphism instance"]
theorem ρ.appIsSplitEpi (U : CosimplicialObject A) : IsSplitEpi (ρ U) := sorry

/-- The source-facing inclusion and projection form a natural retract. -/
@[reassoc, stacks 019I "degenerate cochain natural retract law"]
theorem ι.natTrans_comp_ρ :
    ι.natTrans (A := A) ≫ ρ.natTrans (A := A) =
      𝟙 (degenerateCochainComplex.functor (A := A)) := sorry

namespace ι

/-- The natural source-facing degenerate inclusion, equipped with its retraction. -/
@[stacks 019I "degenerate cochain natural split monomorphism"]
def splitMono : SplitMono (natTrans (A := A)) where
  retraction := ρ.natTrans (A := A)
  id := degenerateCochainComplex.ι.natTrans_comp_ρ (A := A)

/-- The natural source-facing degenerate inclusion is canonically split. -/
@[instance, stacks 019I "degenerate cochain natural split monomorphism instance"]
theorem isSplitMono : IsSplitMono (natTrans (A := A)) := sorry

end ι

namespace ρ

/-- The natural source-facing degenerate projection, equipped with its section. -/
@[stacks 019I "degenerate cochain natural split epimorphism"]
def splitEpi : SplitEpi (natTrans (A := A)) where
  section_ := ι.natTrans (A := A)
  id := degenerateCochainComplex.ι.natTrans_comp_ρ (A := A)

/-- The natural source-facing degenerate projection is canonically split. -/
@[instance, stacks 019I "degenerate cochain natural split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (natTrans (A := A)) := sorry

end ρ

end degenerateCochainComplex

end CategoryTheory.CosimplicialObject
