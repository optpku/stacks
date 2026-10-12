/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Map
public import ReasLib.AlgebraicTopology.DoldKan.QInftyImage
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The degenerate factor of `QInfty`

This leaf owns the chain-level projection from the alternating-face complex to the degreewise
degenerate complex and its split retraction API.

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasZeroObject C] [HasBinaryCoproducts C] [HasImages C]

namespace degenerateComplex

/-- The projector `Q∞` factors through the degree-`n` degenerate subobject. -/
@[stacks 019A "degenerate projection component factorization"]
theorem π.app.factors (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors ((QInfty : K[U] ⟶ K[U]).f n) := sorry

/-- The degree-`n` factor of the `Q∞` projector through the degenerate subobject. -/
@[stacks 019A "degenerate projection component"]
def π.app (U : SimplicialObject C) (n : ℕ) :
    U _⦋n⦌ ⟶ (degenerateSubobject U n : C) :=
  (degenerateSubobject U n).factorThru ((QInfty : K[U] ⟶ K[U]).f n)
    (π.app.factors U n)

/-- The degreewise factor of `Q∞` recovers `Q∞` after the degenerate-subobject inclusion. -/
@[reassoc, stacks 019A "degenerate projection component formula"]
theorem π.app.arrow (U : SimplicialObject C) (n : ℕ) :
    π.app U n ≫ (degenerateSubobject U n).arrow =
      (QInfty : K[U] ⟶ K[U]).f n := sorry

/-- The components of `Q∞` through the degenerate subobjects commute with every relevant
differential. -/
@[stacks 019A "degenerate projection commutes with differentials"]
theorem π.comm (U : SimplicialObject C) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    π.app U i ≫ (D[U]).d i j = (K[U]).d i j ≫ π.app U j := sorry

/-- The canonical factorization `K(U) ⟶ D(U)` of the projector `Q∞`. -/
@[stacks 019A "degenerate projection factorization"]
def π (U : SimplicialObject C) : K[U] ⟶ D[U] where
  f := π.app U
  comm' := π.comm U

/-- The degree-`n` component of the degenerate projection is `π.app`. -/
@[simp, stacks 019A "degenerate projection component projection"]
theorem π.f (U : SimplicialObject C) (n : ℕ) :
    (π U).f n = π.app U n := sorry

/-- The `Q∞` factorization is natural in the simplicial object. -/
@[reassoc, stacks 019A "degenerate projection naturality"]
theorem π.naturality {U V : SimplicialObject C} (f : U ⟶ V) :
    (alternatingFaceMapComplex C).map f ≫ π V = π U ≫ degenerateComplex.map f := sorry

/-- The projection from alternating-face complexes to degenerate complexes is natural. -/
@[stacks 019A "degenerate projection natural transformation"]
def π.natTrans : alternatingFaceMapComplex C ⟶ degenerateComplex.functor (C := C) where
  app U := π U
  naturality _ _ f := π.naturality f

/-- The projection natural transformation has component `π U` at `U`. -/
@[simp, stacks 019A "degenerate projection natural transformation component"]
theorem π.natTrans.app (U : SimplicialObject C) :
    (π.natTrans (C := C)).app U = π U := sorry

/-- Composing the `Q∞` factorization with the degenerate inclusion recovers `Q∞`. -/
@[reassoc, stacks 019A "degenerate projection-inclusion projector formula"]
theorem π_comp_ι (U : SimplicialObject C) :
    π U ≫ degenerateComplex.ι U = QInfty := sorry

/-- The degenerate inclusion followed by the `Q∞` factorization is the identity. -/
@[reassoc, stacks 019A "degenerate inclusion-projection retraction"]
theorem ι_comp_π (U : SimplicialObject C) :
    degenerateComplex.ι U ≫ π U = 𝟙 D[U] := sorry

/-- The natural degenerate inclusion followed by the natural projection is the identity. -/
@[reassoc, stacks 019A "natural degenerate inclusion-projection retraction"]
theorem ι.natTrans_comp_π :
    degenerateComplex.ι.natTrans (C := C) ≫ π.natTrans (C := C) =
      𝟙 (degenerateComplex.functor (C := C)) := sorry

namespace ι

/-- The natural degenerate-complex inclusion, equipped with its natural retraction. -/
@[stacks 019A "natural degenerate-complex split monomorphism"]
def splitMono : SplitMono (degenerateComplex.ι.natTrans (C := C)) where
  retraction := π.natTrans (C := C)
  id := ι.natTrans_comp_π (C := C)

/-- The degenerate-complex inclusion at `U`, equipped with its canonical retraction. -/
@[stacks 019A "degenerate-complex component split monomorphism"]
def appSplitMono (U : SimplicialObject C) : SplitMono (degenerateComplex.ι U) where
  retraction := π U
  id := ι_comp_π U

/-- The natural degenerate-complex inclusion is available to typeclass search as split. -/
@[instance, stacks 019A "natural degenerate-complex split monomorphism instance"]
theorem isSplitMono : IsSplitMono (degenerateComplex.ι.natTrans (C := C)) := sorry

/-- Every component of the degenerate-complex inclusion is available to typeclass search as
split. -/
@[instance, stacks 019A "degenerate-complex component split monomorphism instance"]
theorem appIsSplitMono (U : SimplicialObject C) :
    IsSplitMono (degenerateComplex.ι U) := sorry

end ι

namespace π

/-- The natural degenerate-complex projection, equipped with its natural section. -/
@[stacks 019A "natural degenerate-complex split epimorphism"]
def splitEpi : SplitEpi (π.natTrans (C := C)) where
  section_ := degenerateComplex.ι.natTrans (C := C)
  id := ι.natTrans_comp_π (C := C)

/-- The degenerate-complex projection at `U`, equipped with its canonical section. -/
@[stacks 019A "degenerate-complex component split epimorphism"]
def appSplitEpi (U : SimplicialObject C) : SplitEpi (π U) where
  section_ := degenerateComplex.ι U
  id := ι_comp_π U

/-- The natural degenerate-complex projection is available to typeclass search as split. -/
@[instance, stacks 019A "natural degenerate-complex split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (π.natTrans (C := C)) := sorry

/-- Every component of the degenerate-complex projection is available to typeclass search as
split. -/
@[instance, stacks 019A "degenerate-complex component split epimorphism instance"]
theorem appIsSplitEpi (U : SimplicialObject C) : IsSplitEpi (π U) := sorry

end π

end degenerateComplex

end AlgebraicTopology.DoldKan
