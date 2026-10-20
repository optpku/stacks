module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.HomCodes
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification.SmallCover
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Sites

/-!
# Small Hom codes on the big fppf site

The actual finite-type affine local basis supplies an original-universe site
containing the identity chart. Local arrows are encoded by genuine plus classes
on that small site, and completion arrows by products of their local codes.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Functor.StackificationConstruction
open CategoryTheory.Functor.StackificationConstruction.DescentCompletion
open AlgebraicGeometry.GroupoidsOver.Sheafification

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Stackification

variable {S : Scheme.{u}} {X : Type (u + 1)} [Category.{u} X]
variable (p : X ⥤ Over S) (χ : p.Cleavage)

/-- The actual small finite-type affine local site over a fixed slice object. -/
def localSiteFunctor (U : Over S) : RelativeBasis U.left ⥤ Over U :=
  smallLocalToOver U.left ⋙ U.iteratedSliceBackward

instance localSiteFunctor_isContinuous (U : Over S) :
    (localSiteFunctor U).IsContinuous (relativeBasisTopology U.left)
      ((Scheme.fppfTopology.over S).over U) :=
  Functor.isContinuous_comp _ _ _ (Scheme.fppfTopology.over U.left) _

instance localSiteFunctor_isCocontinuous (U : Over S) :
    (localSiteFunctor U).IsCocontinuous (relativeBasisTopology U.left)
      ((Scheme.fppfTopology.over S).over U) :=
  isCocontinuous_comp _ _ _ (Scheme.fppfTopology.over U.left)

/-- The distinguished chart maps by the actual identity arrow in the iterated slice. -/
def localIdentityIso (U : Over S) :
    (localSiteFunctor U).obj (none : RelativeBasis U.left) ≅ Over.mk (𝟙 U) :=
  Over.isoMk (Over.isoMk (Iso.refl _) (by sorry)) (by sorry)

/-- The chart's structural map is invertible with its specified identity-chart inverse. -/
instance localIdentity_isIso (U : Over S) :
    IsIso ((localSiteFunctor U).obj (none : RelativeBasis U.left)).hom := by
  let e := localIdentityIso U
  have he : e.hom.left = ((localSiteFunctor U).obj (none : RelativeBasis U.left)).hom := by
    have h := Over.w e.hom
    change e.hom.left ≫ 𝟙 U = _ at h
    exact (Category.comp_id _).symm.trans h
  exact he ▸ ((Over.forget U).mapIso e).isIso_hom

/-- A local-arrow Hom type injects into actual original-universe plus-section codes. -/
theorem localizedHomSmall (a b : Localized (Scheme.fppfTopology.over S) p χ) :
    Small.{u} (a ⟶ b) := by
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  exact CategoryTheory.Functor.StackificationConstruction.localizedHomSmall
    (Scheme.fppfTopology.over S) p χ
    (relativeBasisTopology (p.obj a).left) (localSiteFunctor (p.obj a))
    (CoverPreserving.of_isContinuous _ _ _) (none : RelativeBasis (p.obj a).left)

/-- The local-arrow standard fibre Hom type is a subtype of its actual small ambient Hom. -/
theorem localFiberHomSmall {U : Over S}
    (a b : (Localized.projection (Scheme.fppfTopology.over S) p χ).Fiber U) :
    Small.{u} (a ⟶ b) := by
  letI := localizedHomSmall p χ a.1 b.1
  exact small_of_injective (Subtype.val_injective : Function.Injective (fun f : a ⟶ b ↦ f.1))

/-- Completion Hom types inject into actual small local Hom products on a
native small fppf refinement of the two original stored covers. -/
theorem completionHomSmall {U : Over S}
    (a b : DescentCompletion.Object (Scheme.fppfTopology.over S)
      (localFibers (Scheme.fppfTopology.over S) p χ) U) : Small.{u} (a ⟶ b) := by
  let R := smallRefinement (a.cover ⊓ b.cover)
  letI : ∀ i : R.Index, Small.{u}
      (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩ ⟶
        b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩) := fun i ↦
    localFiberHomSmall p χ
      (a.datum.obj ⟨R.object i, R.arrow i, (R.member i).1⟩)
      (b.datum.obj ⟨R.object i, R.arrow i, (R.member i).2⟩)
  exact DescentCompletion.homSmall (Scheme.fppfTopology.over S)
    (localFibers (Scheme.fppfTopology.over S) p χ)
    (Localized.isPrestack (Scheme.fppfTopology.over S) p χ
      (localCleavage (Scheme.fppfTopology.over S) p χ)) a b R

end AlgebraicGeometry.GroupoidsOver.Stackification
