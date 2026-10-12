/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.Syntomic.Basic
public import ReasLib.RingTheory.RingHom.Fiber.Local.CompleteIntersection

/-!
# Syntomic morphisms of schemes

The scheme-level syntomic property is the local form of `RingHom.Syntomic` on
affine neighborhoods.  This leaf owns the definition and its direct pointwise
API.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is syntomic at a point when it is induced by a syntomic ring map on affine
neighborhoods of that point and its image. -/
@[stacks 01UC "syntomic morphism at a point"]
def SyntomicAt (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ V : S.affineOpens,
      ∃ e : U ≤ f ⁻¹ᵁ V,
        RingHom.Syntomic (f.appLE V U e).hom

/-- A syntomic-at hypothesis supplies its affine-neighborhood witness. -/
@[stacks 01UC "affine witness for a syntomic point"]
theorem SyntomicAt.exists_affineNeighborhood
    {x : X} (hx : SyntomicAt f x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Syntomic (f.appLE V U e).hom := sorry

/-- A morphism is syntomic at a point exactly when it has the stated affine-neighborhood
witness. -/
@[stacks 01UC "syntomic-at affine-neighborhood criterion"]
theorem syntomicAt_iff (x : X) :
    SyntomicAt f x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            RingHom.Syntomic (f.appLE V U e).hom := sorry

/-- A scheme morphism is syntomic when it is locally induced by syntomic ring maps. -/
@[stacks 01UC "syntomic scheme morphism"]
abbrev Syntomic : Prop :=
  LocallyOfType RingHom.Syntomic f

namespace Scheme.Hom

/-- The closed fiber local ring at `x` is a complete intersection over the residue field of its
image.  The target prime is the closed point of the target stalk, so this is the scheme-level
bridge to `RingHom.Fiber.IsCompleteIntersectionAt`. -/
@[stacks 00SY "complete-intersection closed fiber at a scheme point"]
def closedFiberCompleteIntersectionAt (x : X) : Prop :=
  RingHom.Fiber.IsCompleteIntersectionAt (f.stalkMap x).hom
    (IsLocalRing.closedPoint (X.presheaf.stalk x))

end Scheme.Hom

/-- A morphism is syntomic exactly when it is syntomic at every point of its source. -/
@[stacks 01UC "pointwise criterion for syntomic morphisms"]
theorem syntomic_iff_forall_syntomicAt :
    Syntomic f ↔ ∀ x : X, SyntomicAt f x := sorry

/-- A scheme over a field is a local complete intersection over that field when its structure
morphism is syntomic. -/
@[stacks 01UC "local complete intersection over a field"]
abbrev IsLocalCompleteIntersectionOver
    (k : Type u) [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Scheme.Spec.obj (Opposite.op <| CommRingCat.of k)) : Prop :=
  Syntomic f

end AlgebraicGeometry
