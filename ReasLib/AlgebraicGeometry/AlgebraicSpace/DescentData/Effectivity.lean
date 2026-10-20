module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData

/-!
# Effective descent data for algebraic spaces over algebraic spaces

Canonical descent data of an algebraic space over `X` is `ofObj`. Effectivity is
membership in the essential image of that functor. The canonical datum is
isomorphic to the pullback of the trivial identity-family datum.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The trivial descent datum of an algebraic space over `X` is its canonical datum
for the singleton identity family. -/
noncomputable def trivial (U : Over X) :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X) :=
  ofObj (fun _ ↦ X) (fun _ ↦ 𝟙 X) U

/-- The unique component of the trivial descent datum is slice pullback along the
identity morphism. -/
theorem trivial_obj_obj (U : Over X) :
    (trivial U).obj ⟨⟩ = (overPullback (𝟙 X)).obj U := sorry

variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/-- Pullback of descent data from the identity family `{id : X → X}` along the
family `f i : Xᵢ i ⟶ X`. -/
noncomputable def trivialPullback :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X) ⥤ DescentData Xᵢ f :=
  Pseudofunctor.DescentData.pullFunctor (F := overPseudofunctor S)
    (p := 𝟙 X) (α := fun _ : I ↦ ⟨⟩) (p' := f) (fun _ ↦ rfl)

/-- The component at `i` of an identity-family datum pulled back along `f` is
slice pullback along `f i`. -/
theorem trivialPullback_obj_obj
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ 𝟙 X)) (i : I) :
    ((trivialPullback Xᵢ f).obj D).obj i = (overPullback (f i)).obj (D.obj ⟨⟩) :=
  sorry

/-- The canonical descent datum of `U` is the pullback of the trivial
descent datum along `{Xᵢ → X} → {id : X → X}`. -/
noncomputable def ofObjIsoPullbackTrivial (U : Over X) :
    ofObj Xᵢ f U ≅ (trivialPullback Xᵢ f).obj (trivial U) :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦
      ((overPseudofunctor S).map (f i).op.toLoc).toFunctor.mapIso
        ((Cat.Hom.toNatIso
          ((overPseudofunctor S).mapId' (𝟙 X).op.toLoc)).app U).symm)
    sorry

/-- The forward component of `ofObjIsoPullbackTrivial` is identity-slice pullback
along each `f i`. -/
theorem ofObjIsoPullbackTrivial_hom_hom (U : Over X) (i : I) :
    (ofObjIsoPullbackTrivial Xᵢ f U).hom.hom i =
      ((overPseudofunctor S).map (f i).op.toLoc).toFunctor.map
        ((Cat.Hom.toNatIso
          ((overPseudofunctor S).mapId' (𝟙 X).op.toLoc)).inv.app U) :=
  sorry

variable {Xᵢ f}

/-- A descent datum relative to `f i : Xᵢ i ⟶ X` is effective when it lies in the
essential image of the canonical pullback descent functor. -/
abbrev IsEffective (D : DescentData Xᵢ f) : Prop :=
  ((overPseudofunctor S).toDescentData f).essImage D

/-- A descent datum is effective exactly when it is isomorphic to the canonical
pullback datum of some algebraic space over `X`. -/
theorem isEffective_iff (D : DescentData Xᵢ f) :
    D.IsEffective ↔ ∃ U : Over X, Nonempty (ofObj Xᵢ f U ≅ D) := sorry

namespace IsEffective

/-- The canonical pullback descent datum of an algebraic space over `X` is
effective. -/
theorem ofObj (U : Over X) : IsEffective (DescentData.ofObj Xᵢ f U) := sorry

/-- Effectivity is preserved by isomorphisms of algebraic-space descent data. -/
theorem ofIso {D E : DescentData Xᵢ f} (e : D ≅ E) (hD : IsEffective D) :
    IsEffective E := sorry

end IsEffective

end AlgebraicGeometry.AlgebraicSpace.DescentData
