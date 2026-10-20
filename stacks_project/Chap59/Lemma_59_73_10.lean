module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (CategoryTheory.OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
variable (c : Cone D)

/- Lemma 59.73.10 (1): constructible sheaves of sets descend through the filtered inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms. -/
@[stacks 09YU] #check (AlgebraicGeometry.Scheme.Etale.Constructible.setHasFilteredDescent
    (D := D) (c := c) :
    ∀ [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
      [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ Type (u + 1)),
        (AlgebraicGeometry.Scheme.smallEtalePullback f).op.HasLeftKanExtension Q],
      IsLimit c →
        AlgebraicGeometry.Scheme.Etale.Constructible.HasFilteredDescent D c
          (fun X F ↦ CategoryTheory.Sheaf.IsConstructibleEtaleSet (X := X)
            (fun {Z} g ↦
              (CategoryTheory.Sheaf.smallEtaleInverseImage g (Type (u + 1))).obj)
            (fun {Z} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant G) F))

/- Lemma 59.73.10 (2): constructible abelian sheaves descend through the filtered inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms. -/
@[stacks 09YU] #check (AlgebraicGeometry.Scheme.Etale.Constructible.addCommGrpHasFilteredDescent
    (D := D) (c := c) :
    ∀ [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
        (AlgebraicGeometry.Scheme.smallEtalePullback f).op.HasLeftKanExtension Q],
      IsLimit c →
        AlgebraicGeometry.Scheme.Etale.Constructible.HasFilteredDescent D c
          (fun X F ↦ CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp (X := X)
            (fun {Z} g ↦
              (CategoryTheory.Sheaf.smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
            (fun {Z} G ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp G) F))

/- Lemma 59.73.10 (3): constructible sheaves of modules descend through the filtered inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms. -/
@[stacks 09YU] #check (AlgebraicGeometry.Scheme.Etale.Constructible.moduleHasFilteredDescent
    (D := D) (c := c) :
    ∀ {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ]
      [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
      [∀ (S : Scheme.{u}) (U : S.Etale),
        HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
      [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
        (AlgebraicGeometry.Scheme.smallEtalePullback f).op.HasLeftKanExtension Q],
      IsLimit c →
        AlgebraicGeometry.Scheme.Etale.Constructible.HasFilteredDescent D c
          (fun X F ↦ CategoryTheory.Sheaf.IsConstructibleEtaleModule (X := X)
            (fun {Z} g ↦
              (CategoryTheory.Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
            (fun {Z} G ↦ CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule G) F))
