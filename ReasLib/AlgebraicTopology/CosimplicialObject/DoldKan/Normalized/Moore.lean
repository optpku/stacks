module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Opposite
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
# Transported normalized Moore cochains

This leaf transports the simplicial normalized Moore equivalence and its canonical retract across
opposites. It does not depend on the quotient presentation of normalized cochains.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace normalizedMooreCochainComplex

/-- The transported Dold--Kan equivalence before comparison with the quotient-defined normalized
cochain complex. -/
@[stacks 019I "transported cosimplicial Dold-Kan equivalence"]
noncomputable def equivalence : CosimplicialObject A ≌ CochainComplex A ℕ :=
  (((cosimplicialSimplicialEquiv A).trans
      (Abelian.DoldKan.equivalence : SimplicialObject Aᵒᵖ ≌ ChainComplex Aᵒᵖ ℕ)).rightOp).trans
    (HomologicalComplex.unopEquivalence A (ComplexShape.down ℕ))

/-- The functor of the transported Dold--Kan equivalence. -/
@[stacks 019I "transported normalized cochain functor"]
abbrev functor : CosimplicialObject A ⥤ CochainComplex A ℕ := equivalence.functor

end normalizedMooreCochainComplex

/-- The transported normalized Moore cochain complex of a cosimplicial object. -/
@[stacks 019I "transported normalized Moore cochain complex"]
abbrev normalizedMooreCochainComplex (U : CosimplicialObject A) : CochainComplex A ℕ :=
  normalizedMooreCochainComplex.functor.obj U

namespace normalizedMooreCochainComplex

namespace opposite

/-- The transported normalized Moore inclusion into the opposite model of the alternating
coface complex. -/
@[stacks 019I "transported normalized inclusion in the opposite model"]
def ι (U : CosimplicialObject A) :
    normalizedMooreCochainComplex U ⟶ DoldKan.alternatingCoface.opposite.complex.obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((PInftyToNormalizedMooreComplex U.op).op)

/-- The projection from the opposite-simplicial alternating complex onto the transported
normalized Moore model. -/
@[stacks 019I "transported normalized projection in the opposite model"]
def π (U : CosimplicialObject A) :
    DoldKan.alternatingCoface.opposite.complex.obj U ⟶ normalizedMooreCochainComplex U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((inclusionOfMooreComplexMap U.op).op)

end opposite

/-- The transported normalized Moore inclusion into the alternating coface complex. -/
@[stacks 019I "transported normalized cochain inclusion"]
def ι (U : CosimplicialObject A) :
    normalizedMooreCochainComplex U ⟶ (alternatingCofaceMapComplex A).obj U :=
  opposite.ι U ≫ (DoldKan.alternatingCoface.opposite.appIso U).inv

/-- The projection from the alternating coface complex onto the transported normalized Moore
model. -/
@[stacks 019I "transported normalized cochain projection"]
def π (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ normalizedMooreCochainComplex U :=
  (DoldKan.alternatingCoface.opposite.appIso U).hom ≫ opposite.π U

/-- The degree-`n` component of the transported normalized inclusion is the unopposite simplicial
normalized projection. -/
@[simp, stacks 019I "transported normalized cochain inclusion component"]
theorem ι.f (U : CosimplicialObject A) (n : ℕ) :
    (ι U).f n = ((PInftyToNormalizedMooreComplex U.op).f n).unop := sorry

/-- Naturality of the transported normalized inclusion. -/
@[reassoc, stacks 019I "transported normalized cochain inclusion naturality"]
theorem ι.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    functor.map f ≫ ι V =
      ι U ≫ (alternatingCofaceMapComplex A).map f := sorry

/-- The transported normalized inclusions form a natural transformation to alternating
cochains. -/
@[stacks 019I "transported normalized cochain inclusion natural transformation"]
def ι.natTrans : functor ⟶ alternatingCofaceMapComplex A where
  app U := ι U
  naturality _ _ f := ι.naturality f

/-- The transported normalized inclusion natural transformation has component `ι U`. -/
@[simp, stacks 019I "transported normalized inclusion natural transformation component"]
theorem ι.natTrans.app (U : CosimplicialObject A) :
    (ι.natTrans (A := A)).app U = ι U := sorry

/-- The degree-`n` component of the transported normalized projection is the unopposite simplicial
normalized inclusion. -/
@[simp, stacks 019I "transported normalized cochain projection component"]
theorem π.f (U : CosimplicialObject A) (n : ℕ) :
    (π U).f n = ((inclusionOfMooreComplexMap U.op).f n).unop := sorry

/-- Naturality of the transported normalized projection. -/
@[reassoc, stacks 019I "transported normalized cochain projection naturality"]
theorem π.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫ π V =
      π U ≫ functor.map f := sorry

/-- The transported normalized projections form a natural transformation from alternating
cochains. -/
@[stacks 019I "transported normalized cochain projection natural transformation"]
def π.natTrans : alternatingCofaceMapComplex A ⟶ functor where
  app U := π U
  naturality _ _ f := π.naturality f

/-- The transported normalized projection natural transformation has component `π U`. -/
@[simp, stacks 019I "transported normalized projection natural transformation component"]
theorem π.natTrans.app (U : CosimplicialObject A) :
    (π.natTrans (A := A)).app U = π U := sorry

/-- The transported normalized inclusion is a section of the transported normalized
projection. -/
@[reassoc, stacks 019I "transported normalized cochain retract law"]
theorem ι_comp_π (U : CosimplicialObject A) :
    ι U ≫ π U = 𝟙 (normalizedMooreCochainComplex U) := sorry

/-- A transported normalized Moore inclusion component, equipped with its retraction. -/
@[stacks 019I "transported normalized cochain component split monomorphism"]
def ι.appSplitMono (U : CosimplicialObject A) : SplitMono (ι U) where
  retraction := π U
  id := ι_comp_π U

/-- Every transported normalized Moore inclusion component is canonically split. -/
@[instance, stacks 019I "transported normalized cochain component split monomorphism instance"]
theorem ι.appIsSplitMono (U : CosimplicialObject A) : IsSplitMono (ι U) := sorry

/-- A transported normalized Moore projection component, equipped with its section. -/
@[stacks 019I "transported normalized cochain component split epimorphism"]
def π.appSplitEpi (U : CosimplicialObject A) : SplitEpi (π U) where
  section_ := ι U
  id := ι_comp_π U

/-- Every transported normalized Moore projection component is canonically split. -/
@[instance, stacks 019I "transported normalized cochain component split epimorphism instance"]
theorem π.appIsSplitEpi (U : CosimplicialObject A) : IsSplitEpi (π U) := sorry

/-- The transported normalized inclusion and projection form a natural retract. -/
@[reassoc, stacks 019I "transported normalized cochain natural retract law"]
theorem ι.natTrans_comp_π :
    ι.natTrans (A := A) ≫ π.natTrans (A := A) = 𝟙 (functor (A := A)) := sorry

namespace ι

/-- The natural transported normalized Moore inclusion, equipped with its retraction. -/
@[stacks 019I "transported normalized cochain natural split monomorphism"]
def splitMono : SplitMono (natTrans (A := A)) where
  retraction := π.natTrans (A := A)
  id := normalizedMooreCochainComplex.ι.natTrans_comp_π (A := A)

/-- The natural transported normalized Moore inclusion is canonically split. -/
@[instance, stacks 019I "transported normalized cochain natural split monomorphism instance"]
theorem isSplitMono : IsSplitMono (natTrans (A := A)) := sorry

end ι

namespace π

/-- The natural transported normalized Moore projection, equipped with its section. -/
@[stacks 019I "transported normalized cochain natural split epimorphism"]
def splitEpi : SplitEpi (natTrans (A := A)) where
  section_ := ι.natTrans (A := A)
  id := normalizedMooreCochainComplex.ι.natTrans_comp_π (A := A)

/-- The natural transported normalized Moore projection is canonically split. -/
@[instance, stacks 019I "transported normalized cochain natural split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (natTrans (A := A)) := sorry

end π

end normalizedMooreCochainComplex

end CategoryTheory.CosimplicialObject
