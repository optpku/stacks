/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.UniversalProperty
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Truncation
public import ReasLib.CategoryTheory.Functor.RightKanExtension.LimitMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Successive coskeleton extensions

Right Kan extension along an inclusion of truncated simplex categories is the canonical one-step
extension used in explicit matching-object constructions. Arbitrary truncation levels are owned by
`Truncated.trunc.cosk.{to,adj,homEquiv,ranIso,adjunction}`; this leaf only exposes the successor
specialization and its matching-object comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace successor

/-- The opposite one-step inclusion from level `n` to level `n + 1`. -/
@[stacks 0189 "one-step truncated-simplex inclusion"]
abbrev inclusion (n : ℕ) :
    (SimplexCategory.Truncated n)ᵒᵖ ⥤
      (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
  (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op

/-- The top object indexing the successor matching diagram. -/
@[stacks 0189 "successor top simplex"]
abbrev top (n : ℕ) : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
  op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))

namespace matching

/-- The finite structured-arrow matching diagram for a successor extension. -/
@[stacks 0189 "successor matching diagram"]
abbrev diagram (n : ℕ)
    (U : SimplicialObject.Truncated C n) :
    StructuredArrow (top n) (inclusion n) ⥤ C :=
  StructuredArrow.proj (top n) (inclusion n) ⋙ U

/-- The equivalence between the finite successor index and the canonical matching index. -/
@[stacks 0189 "successor matching diagram comparison"]
noncomputable def diagramIso (n : ℕ)
    (U : SimplicialObject.Truncated C n) :
    (SimplexCategory.Truncated.incl.structuredArrowEquiv n (n + 1) (Nat.le_succ n)
      (top n)).functor ⋙ CategoryTheory.SimplicialObject.Truncated.matching.diagram U ≅
      diagram n U :=
  Iso.refl _

/-- A limit over the successor structured-arrow category supplies the canonical matching
object, by reversing the indexing-category equivalence.

This is a low-priority fallback only.  The canonical `HasMatchingObjects.hasLimit` instance owns
the matching diagram whenever it is available; this bridge is used when a caller has only the
successor-index limit.  Keeping the fallback below the canonical owner avoids changing the chosen
`matching.object` in downstream files that import both interfaces. -/
@[stacks 0189 "matching limit from the successor index"]
noncomputable instance (priority := 100) hasLimit (n : ℕ) (U : SimplicialObject.Truncated C n)
    [HasLimit (diagram n U)] :
    HasLimit (CategoryTheory.SimplicialObject.Truncated.matching.diagram U) :=
  @Limits.hasLimit_of_equivalence_comp _ _ _ _ _ _
    (CategoryTheory.SimplicialObject.Truncated.matching.diagram U)
    (SimplexCategory.Truncated.incl.structuredArrowEquiv n (n + 1) (Nat.le_succ n)
      (top n))
    (Limits.hasLimit_of_iso (diagramIso n U).symm)

/-- The limit comparison from the finite successor index to the canonical matching object. -/
@[stacks 0189 "successor matching-index limit comparison"]
noncomputable def objectIso (n : ℕ)
    (U : SimplicialObject.Truncated C n)
    [HasLimit (diagram n U)] :
    limit (diagram n U) ≅
      CategoryTheory.SimplicialObject.Truncated.matching.object U :=
  Limits.HasLimit.isoOfEquivalence
    (SimplexCategory.Truncated.incl.structuredArrowEquiv n (n + 1) (Nat.le_succ n)
      (top n))
    (diagramIso n U)

end matching

end successor

namespace HasMatchingObjects

/- The one-step right Kan extension is pointwise at lower degrees by full faithfulness of the
  truncation inclusion, and at the new top degree by the matching limit.  Keeping these bridges
  here makes `HasMatchingObjects` the reusable existence owner instead of forcing callers to
  rebuild a structured-arrow argument for every successor construction.  Mathlib already derives
  an ordinary Kan extension from a pointwise one, so only the pointwise instances belong here. -/

/-- Matching limits provide the pointwise one-step coskeleton for each truncated object.

This is a proposition-valued bridge: the concrete right Kan extension remains Mathlib's
canonical pointwise construction, while the matching-limit hypothesis is the only public
existence input. -/
@[stacks 0187 "matching objects imply pointwise one-step coskeletons"]
noncomputable instance hasPointwiseCoskeletonSucc (n : ℕ)
    {C : Type u} [Category.{v} C] [HasMatchingObjects C n]
    (U : SimplicialObject.Truncated C n) :
    Between.HasPointwiseCoskeleton U (n + 1) (Nat.le_succ n) := sorry

/-- Category-wide pointwise successor existence, assembled from the canonical per-object bridge. -/
@[stacks 0187 "category-wide pointwise successor coskeletons"]
noncomputable instance hasPointwiseCoskeletonsSucc (n : ℕ)
    {C : Type u} [Category.{v} C] [HasMatchingObjects C n] :
    Between.HasPointwiseCoskeletons C n (n + 1) (Nat.le_succ n) := sorry

end HasMatchingObjects

namespace trunc.cosk

/-- The canonical one-step extension of an `n`-truncated simplicial object. -/
@[stacks 0189 "one-step coskeleton extension"]
noncomputable abbrev succ (n : ℕ)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n (n + 1) (Nat.le_succ n)] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C (n + 1) :=
  trunc.cosk.functor n (n + 1) (Nat.le_succ n)

/-- The one-step extension's universal Hom-equivalence. -/
@[stacks 0189 "one-step coskeleton Hom equivalence"]
noncomputable def succ.homEquiv (n : ℕ)
    [SimplicialObject.Truncated.Between.HasCoskeletons C n (n + 1) (Nat.le_succ n)]
    (U : SimplicialObject.Truncated C n)
    (V : SimplicialObject.Truncated C (n + 1)) :
    ((Truncated.trunc C (n + 1) n (Nat.le_succ n)).obj V ⟶ U) ≃
      (V ⟶ (succ n).obj U) :=
  trunc.cosk.homEquiv n (n + 1) (Nat.le_succ n) U V

/-- The top-degree value of the one-step extension is canonically the matching object. -/
@[stacks 0189 "top degree is the matching object"]
noncomputable def succ.top.iso (n : ℕ)
    (U : SimplicialObject.Truncated C n)
    [SimplicialObject.Truncated.Between.HasPointwiseCoskeleton U (n + 1)
      (Nat.le_succ n)] :
    ((successor.inclusion n).rightKanExtension U).obj (successor.top n) ≅
      matching.object U :=
  Functor.RightKanExtension.objIsoLimit
      (successor.inclusion n) U (successor.top n) ≪≫
    successor.matching.objectIso n U

/-- The matching-family functor is represented by the top degree of the one-step extension. -/
@[stacks 0189 "top degree represents matching families"]
noncomputable def succ.top.representableBy (n : ℕ)
    (U : SimplicialObject.Truncated C n)
    [SimplicialObject.Truncated.Between.HasPointwiseCoskeleton U (n + 1)
      (Nat.le_succ n)] :
    (matching.FaceFamily.presheaf U).RepresentableBy
      (((successor.inclusion n).rightKanExtension U).obj (successor.top n)) :=
  (matching.object.representableBy U).ofIsoObj (succ.top.iso n U)

/-- The canonical one-step coskeleton, equipped as the matching extension represented by the
canonical matching object. Its object, old-degree comparison, and top-degree comparison are
explicit; the right-Kan-extension and structure-map fields are proposition-valued laws. -/
@[stacks 0189 "one-step coskeleton as a matching extension"]
noncomputable def succ.extension (n : ℕ)
    (U : SimplicialObject.Truncated C n)
    [SimplicialObject.Truncated.Between.HasPointwiseCoskeleton U (n + 1)
      (Nat.le_succ n)] :
    matching.Extension (matching.object.representableBy U) where
  obj := (successor.inclusion n).rightKanExtension U
  truncIso := Functor.RightKanExtension.counitIso
    (successor.inclusion n) U
  topIso := succ.top.iso n U
  isRightKanExtension := sorry
  face_eq_π := sorry
  degeneracy_eq_σ := sorry

end trunc.cosk

end CategoryTheory.SimplicialObject.Truncated

section

variable {C : Type u} [Category.{v} C] (n : ℕ)
variable [CategoryTheory.SimplicialObject.Truncated.HasMatchingObjects C n]

#synth CategoryTheory.SimplicialObject.Truncated.Between.HasPointwiseCoskeletons
  C n (n + 1) (Nat.le_succ n)
#synth CategoryTheory.SimplicialObject.Truncated.Between.HasCoskeletons
  C n (n + 1) (Nat.le_succ n)

end
