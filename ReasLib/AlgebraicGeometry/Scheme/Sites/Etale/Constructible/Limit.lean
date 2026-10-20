module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.Composition
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale.Constructible

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable (c : Cone D)

/-- The canonical comparison from inverse image along a cone projection to inverse image
along a later-stage transition followed by the later cone projection. -/
noncomputable def stagePullbackIso
    {A : Type v} [Category.{w} A]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology A]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ A),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    {i j : I} (hij : i ≤ j) :
    (CategoryTheory.Sheaf.smallEtaleInverseImage (c.π.app (OrderDual.toDual i)) A) ≅
      (CategoryTheory.Sheaf.smallEtaleInverseImage
          (OrderDualInverseSystem.transitionMap D hij) A) ⋙
        (CategoryTheory.Sheaf.smallEtaleInverseImage (c.π.app (OrderDual.toDual j)) A) := by
  exact eqToIso (congrArg (fun h : c.pt ⟶ D.obj (OrderDual.toDual i) ↦
      CategoryTheory.Sheaf.smallEtaleInverseImage h A)
      (c.w (homOfLE (OrderDual.toDual_le_toDual.mpr hij))).symm) ≪≫
    AlgebraicGeometry.Scheme.smallEtaleSheafPullbackCompIso
      (c.π.app (OrderDual.toDual j))
      (OrderDualInverseSystem.transitionMap D hij)

/-- A coefficient-valued sheaf property satisfies filtered descent when objects, morphisms,
and equality of parallel morphisms descend along the directed inverse system. -/
def HasFilteredDescent
    {A : Type v} [Category.{w} A]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology A]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ A),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (P : ∀ S : Scheme.{u}, Sheaf S.smallEtaleTopology A → Prop) : Prop :=
  (∀ F : Sheaf c.pt.smallEtaleTopology A, P c.pt F →
    ∃ (i : I) (G : Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology A),
      P (D.obj (OrderDual.toDual i)) G ∧
        Nonempty ((CategoryTheory.Sheaf.smallEtaleInverseImage
          (c.π.app (OrderDual.toDual i)) A).obj G ≅ F)) ∧
  (∀ (i : I) (F G : Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology A),
    P (D.obj (OrderDual.toDual i)) F → P (D.obj (OrderDual.toDual i)) G →
    ∀ α : (CategoryTheory.Sheaf.smallEtaleInverseImage
      (c.π.app (OrderDual.toDual i)) A).obj F ⟶
      (CategoryTheory.Sheaf.smallEtaleInverseImage
        (c.π.app (OrderDual.toDual i)) A).obj G,
      ∃ (j : I) (hij : i ≤ j)
        (β : (CategoryTheory.Sheaf.smallEtaleInverseImage
          (OrderDualInverseSystem.transitionMap D hij) A).obj F ⟶
          (CategoryTheory.Sheaf.smallEtaleInverseImage
            (OrderDualInverseSystem.transitionMap D hij) A).obj G),
        α = (stagePullbackIso D c hij).hom.app F ≫
          (CategoryTheory.Sheaf.smallEtaleInverseImage
            (c.π.app (OrderDual.toDual j)) A).map β ≫
          (stagePullbackIso D c hij).inv.app G) ∧
  (∀ (i : I) (F G : Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology A),
    P (D.obj (OrderDual.toDual i)) F → P (D.obj (OrderDual.toDual i)) G →
    ∀ α β : F ⟶ G,
      (CategoryTheory.Sheaf.smallEtaleInverseImage
        (c.π.app (OrderDual.toDual i)) A).map α =
        (CategoryTheory.Sheaf.smallEtaleInverseImage
          (c.π.app (OrderDual.toDual i)) A).map β →
      ∃ (j : I) (hij : i ≤ j),
        (CategoryTheory.Sheaf.smallEtaleInverseImage
          (OrderDualInverseSystem.transitionMap D hij) A).map α =
          (CategoryTheory.Sheaf.smallEtaleInverseImage
            (OrderDualInverseSystem.transitionMap D hij) A).map β)

/-- The filtered descent predicate is equivalent to its object, morphism, and equality clauses. -/
theorem hasFilteredDescent_iff
    {A : Type v} [Category.{w} A]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology A]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ A),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (P : ∀ S : Scheme.{u}, Sheaf S.smallEtaleTopology A → Prop) :
    HasFilteredDescent D c P ↔
      (∀ F : Sheaf c.pt.smallEtaleTopology A, P c.pt F →
        ∃ (i : I) (G : Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology A),
          P (D.obj (OrderDual.toDual i)) G ∧
            Nonempty ((CategoryTheory.Sheaf.smallEtaleInverseImage
              (c.π.app (OrderDual.toDual i)) A).obj G ≅ F)) ∧
      (∀ (i : I) (F G : Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology A),
        P (D.obj (OrderDual.toDual i)) F → P (D.obj (OrderDual.toDual i)) G →
        ∀ α : (CategoryTheory.Sheaf.smallEtaleInverseImage
          (c.π.app (OrderDual.toDual i)) A).obj F ⟶
          (CategoryTheory.Sheaf.smallEtaleInverseImage
            (c.π.app (OrderDual.toDual i)) A).obj G,
          ∃ (j : I) (hij : i ≤ j)
            (β : (CategoryTheory.Sheaf.smallEtaleInverseImage
              (OrderDualInverseSystem.transitionMap D hij) A).obj F ⟶
              (CategoryTheory.Sheaf.smallEtaleInverseImage
                (OrderDualInverseSystem.transitionMap D hij) A).obj G),
            α = (stagePullbackIso D c hij).hom.app F ≫
              (CategoryTheory.Sheaf.smallEtaleInverseImage
                (c.π.app (OrderDual.toDual j)) A).map β ≫
              (stagePullbackIso D c hij).inv.app G) ∧
      (∀ (i : I) (F G : Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology A),
        P (D.obj (OrderDual.toDual i)) F → P (D.obj (OrderDual.toDual i)) G →
        ∀ α β : F ⟶ G,
          (CategoryTheory.Sheaf.smallEtaleInverseImage
            (c.π.app (OrderDual.toDual i)) A).map α =
            (CategoryTheory.Sheaf.smallEtaleInverseImage
              (c.π.app (OrderDual.toDual i)) A).map β →
          ∃ (j : I) (hij : i ≤ j),
            (CategoryTheory.Sheaf.smallEtaleInverseImage
              (OrderDualInverseSystem.transitionMap D hij) A).map α =
              (CategoryTheory.Sheaf.smallEtaleInverseImage
                (OrderDualInverseSystem.transitionMap D hij) A).map β) := sorry

/-- Constructible étale sheaves of sets on a directed inverse limit of quasi-compact,
quasi-separated schemes with affine transition morphisms satisfy filtered descent. -/
theorem setHasFilteredDescent
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    HasFilteredDescent D c (fun X F ↦ IsConstructibleEtaleSet (X := X)
      (fun {Z} g ↦ (CategoryTheory.Sheaf.smallEtaleInverseImage g (Type (u + 1))).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstant G) F) := sorry

/-- Constructible étale sheaves of abelian groups on a directed inverse limit of
quasi-compact, quasi-separated schemes with affine transition morphisms satisfy filtered descent. -/
theorem addCommGrpHasFilteredDescent
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    HasFilteredDescent D c (fun X F ↦ IsConstructibleEtaleAddCommGrp (X := X)
      (fun {Z} g ↦ (CategoryTheory.Sheaf.smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
      (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) := sorry

/-- Constructible étale sheaves of finite-type modules on a directed inverse limit of
quasi-compact, quasi-separated schemes with affine transition morphisms satisfy filtered descent
over a Noetherian ring. -/
theorem moduleHasFilteredDescent
    {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ]
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ (S : Scheme.{u}) (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    HasFilteredDescent D c (fun X F ↦ IsConstructibleEtaleModule (X := X)
      (fun {Z} g ↦ (CategoryTheory.Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
      (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F) := sorry

end AlgebraicGeometry.Scheme.Etale.Constructible
