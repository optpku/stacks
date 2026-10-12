/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.UniversalProperty
public import ReasLib.CategoryTheory.Adjunction.Representability

/-!
@stack 0187

# One-step matching extensions and the partial right adjoint

Representability of matching face families gives the source of the partial right adjoint to
one-step truncation. Every concrete extension is canonically isomorphic to the selected object.
-/

@[expose] public section

open CategoryTheory Opposite
open SimplexCategory.Truncated
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace matching.FaceFamily

namespace partialRightAdjoint

/-- Representability of the next matching-family functor places `U` in the domain of the partial
right adjoint to one-step truncation. -/
@[stacks 0187 "one-step truncation partial right adjoint"]
theorem objDefined {n : ℕ} {U : SimplicialObject.Truncated C n}
    (hrep : (FaceFamily.presheaf U).IsRepresentable) :
    (Truncated.trunc C (n + 1) n).rightAdjointObjIsDefined U := sorry

/-- A truncated simplicial object with representable next matching families, regarded as an
object in the source of the partial right adjoint to one-step truncation. -/
@[stacks 0187 "source of the one-step partial right adjoint"]
def source {n : ℕ} {U : SimplicialObject.Truncated C n}
    (hrep : (FaceFamily.presheaf U).IsRepresentable) :
    (Truncated.trunc C (n + 1) n).PartialRightAdjointSource :=
  ⟨U, objDefined hrep⟩

end partialRightAdjoint

end matching.FaceFamily

namespace matching.Extension.partialRightAdjoint

/-- A concrete one-step matching extension is canonically isomorphic to the object selected by
the partial right adjoint to one-step truncation. -/
@[stacks 0187 "one-step extension and partial right-adjoint comparison"]
noncomputable def iso {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (matching.FaceFamily.presheaf U).RepresentableBy T}
    (E : matching.Extension R) :
    E.obj ≅
      (Truncated.trunc C (n + 1) n).partialRightAdjointObj
        (matching.FaceFamily.partialRightAdjoint.source R.isRepresentable) :=
  Functor.partialRightAdjoint.iso
    (matching.FaceFamily.partialRightAdjoint.source R.isRepresentable)
    E.representableBy

/-- The forward comparison carries the concrete extension's restriction map to the universal
element selected by the partial right adjoint. -/
@[simp, stacks 0187 "one-step extension partial right-adjoint forward formula"]
theorem iso.hom_apply {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (matching.FaceFamily.presheaf U).RepresentableBy T}
    (E : matching.Extension R) :
    (Truncated.trunc C (n + 1) n).partialRightAdjointHomEquiv
        (Y := matching.FaceFamily.partialRightAdjoint.source R.isRepresentable)
        (iso E).hom =
      E.truncIso.hom := sorry

/-- The inverse comparison carries the chosen partial-right-adjoint universal element back to
the Hom equivalence of the concrete extension. -/
@[simp, stacks 0187 "one-step extension partial right-adjoint inverse formula"]
theorem iso.inv_apply {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (matching.FaceFamily.presheaf U).RepresentableBy T}
    (E : matching.Extension R) :
    E.homEquiv (iso E).inv =
      (Truncated.trunc C (n + 1) n).partialRightAdjointHomEquiv
        (Y := matching.FaceFamily.partialRightAdjoint.source R.isRepresentable)
        (𝟙 _) := sorry

end matching.Extension.partialRightAdjoint

end CategoryTheory.SimplicialObject.Truncated
