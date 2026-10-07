module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Stability of valuative covering families

The `V`-covering predicate is stable under refinement, isomorphisms,
composition, and base change.  These closure statements are kept in a small
leaf separate from the concrete finite-family constructors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A family is a `V` cover exactly when it admits a refining `V` cover. -/
@[stacks 0ETI]
theorem isVCovering_iff_exists_refinement
    {ι : Type v} {T : Scheme.{u}} (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T) :
    IsVCovering T family map ↔
      ∃ (κ : Type v) (refining : κ → Scheme.{u}) (refiningMap : ∀ k, refining k ⟶ T),
        IsVCovering T refining refiningMap ∧
          SemiRepresentableFamily.Over.Refines
            (SemiRepresentableFamily.Over.ofArrows refining refiningMap)
            (SemiRepresentableFamily.Over.ofArrows family map) := sorry

/-- A family is a `V` cover exactly when its coproduct map, viewed as a singleton
family, is a `V` cover. -/
@[stacks 0ETI]
theorem isVCovering_iff_sigmaDesc
    {ι : Type v} {T : Scheme.{u}} [Small.{u} ι] (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T) :
    IsVCovering T family map ↔
      IsVCovering T (fun _ : PUnit ↦ ∐ family) (fun _ ↦ Limits.Sigma.desc map) := sorry

variable {T T' : Scheme.{u}} {ι : Type v} {κ : ι → Type w}

/-- An isomorphism is a singleton `V` cover. -/
@[stacks 0ETJ]
theorem isVCovering_singleton_of_isIso (f : T' ⟶ T) [IsIso f] :
    IsVCovering T (fun _ : Unit ↦ T') (fun _ ↦ f) := sorry

namespace IsVCovering

/-- `V` covers are stable under base change. -/
@[stacks 0ETJ]
theorem pullback (family : ι → Scheme.{u}) (map : ∀ i, family i ⟶ T)
    (hfamily : IsVCovering T family map) (g : T' ⟶ T) :
    IsVCovering T' (fun i : ι ↦ pullback (map i) g)
      (fun i ↦ pullback.snd (map i) g) := sorry

/-- `V` covers are closed under indexed composition. -/
@[stacks 0ETJ]
theorem comp (family : ι → Scheme.{u}) (map : ∀ i, family i ⟶ T)
    (refining : ∀ i, κ i → Scheme.{u}) (refiningMap : ∀ i j, refining i j ⟶ family i)
    (hfamily : IsVCovering T family map)
    (hrefining : ∀ i, IsVCovering (family i) (refining i) (refiningMap i)) :
    IsVCovering T (fun p : Sigma κ ↦ refining p.1 p.2)
      (fun p ↦ refiningMap p.1 p.2 ≫ map p.1) := sorry

end IsVCovering

end AlgebraicGeometry
