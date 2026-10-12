/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Associativity
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.StdSimplex
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Constant.Restriction

/-!
# Degreewise universal property of simplicial internal hom

A representation of the simplicial mapping-object presheaf restricts in degree `n` to the
presheaf represented by maps out of the copower indexed by `U ⊗ Δ[n]`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]
/-- The degree-`n` test presheaf for the mapping object from `U` to `T`. It sends `X` to maps
from the copower indexed by `U ⊗ Δ[n]` of the constant simplicial object on `X` into `T`. -/
@[stacks 017L "degreewise internal-hom test presheaf"]
def internalHom.degree.presheaf
    (U : SSet.{uS}) (T : SimplicialObject C) (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C] :
    Cᵒᵖ ⥤ Type vC :=
  @internalHom.constRestriction C _ (U ⊗ Δ[n]) T
    (HasConstCopowers.tensor U (Δ[n] : SSet.{uS}) C)

/-- A representation of the global mapping-object presheaf induces the expected degree-`n`
equivalence, with the tensor-copower associativity made explicit. -/
@[stacks 017L "degreewise internal-hom hom equivalence"]
def internalHom.degree.homEquiv
    {U : SSet.{uS}} {T M : SimplicialObject C} (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C]
    (R : (internalHom.presheaf U T).RepresentableBy M) {X : C} :
    (X ⟶ M.obj (op (SimplexCategory.mk n))) ≃
      (internalHom.degree.presheaf U T n).obj (op X) :=
  ((copower.stdSimplex.homEquiv n X M).symm.trans R.homEquiv).trans
    ((Functor.indexedCoprod.tensorIso U (Δ[n] : SSet.{uS}) ((const C).obj X)).symm.homCongr
      (Iso.refl T))

/-- The degree equivalence induced by a global representation is natural in its test object. -/
@[stacks 017L "degreewise internal-hom naturality"]
theorem internalHom.degree.homEquiv.comp
    {U : SSet.{uS}} {T M : SimplicialObject C} (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C]
    (R : (internalHom.presheaf U T).RepresentableBy M) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ M.obj (op (SimplexCategory.mk n))) :
    internalHom.degree.homEquiv n R (f ≫ g) =
      (internalHom.degree.presheaf U T n).map f.op
        (internalHom.degree.homEquiv n R g) := sorry

/-- A representation of the mapping-object presheaf represents its degree-`n` test presheaf by
the degree-`n` component of the same simplicial object. -/
@[stacks 017L "degreewise internal-hom representability"]
def internalHom.degree.representableBy
    {U : SSet.{uS}} {T M : SimplicialObject C} (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C]
    (R : (internalHom.presheaf U T).RepresentableBy M) :
    (internalHom.degree.presheaf U T n).RepresentableBy
      (M.obj (op (SimplexCategory.mk n))) where
  homEquiv := internalHom.degree.homEquiv n R
  homEquiv_comp := internalHom.degree.homEquiv.comp n R

/-- The hom equivalence of the degreewise representation is the canonical composite through
standard-simplex evaluation and tensor-copower associativity. -/
@[simp, stacks 017L "degreewise internal-hom equivalence computation"]
theorem internalHom.degree.representableBy.homEquiv
    {U : SSet.{uS}} {T M : SimplicialObject C} (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C]
    (R : (internalHom.presheaf U T).RepresentableBy M) {X : C}
    (f : X ⟶ M.obj (op (SimplexCategory.mk n))) :
    (internalHom.degree.representableBy n R).homEquiv f =
      internalHom.degree.homEquiv n R f := sorry

/-- The chosen internal mapping object has the canonical expected representation in every
simplicial degree. -/
@[stacks 017L "degreewise representation"]
noncomputable def internalHom.degree.representable
    (U : SSet.{uS}) (T : SimplicialObject C) (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C]
    [Functor.IsRepresentable (internalHom.presheaf U T)] :
    (internalHom.degree.presheaf U T n).RepresentableBy
      ((internalHom U T).obj (op (SimplexCategory.mk n))) :=
  internalHom.degree.representableBy n (internalHom.presheaf U T).representableBy

/-- Representability of the global mapping-object presheaf automatically implies
representability of every degree test presheaf. -/
@[stacks 017L "degreewise internal-hom representability instance"]
instance internalHom.degree.isRepresentable
    (U : SSet.{uS}) (T : SimplicialObject C) (n : ℕ)
    [HasCopowers U C] [HasConstCopowers (Δ[n] : SSet.{uS}) C]
    [Functor.IsRepresentable (internalHom.presheaf U T)] :
    Functor.IsRepresentable (internalHom.degree.presheaf U T n) :=
  (internalHom.degree.representable U T n).isRepresentable

end CategoryTheory.SimplicialObject
