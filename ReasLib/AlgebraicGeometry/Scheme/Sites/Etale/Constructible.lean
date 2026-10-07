module

public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.Topology.Stratification.Partition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Constructible

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Topology

universe u v w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/-- A sheaf on the small étale site is constructible relative to a supplied local-constancy
predicate when every affine open admits a finite partition into constructible locally closed
subschemes on which the corresponding restrictions satisfy that predicate. -/
def IsConstructibleEtale
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology D → Sheaf Y.smallEtaleTopology D)
    (locallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology D → Prop)
    (F : Sheaf X.smallEtaleTopology D) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U →
    ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set U.toScheme) ∧
          let T : LocallyCloseds U.toScheme :=
            ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
          locallyConstant (restrict (Scheme.LocallyClosedReduction.ι T ≫ U.ι) F)

/-- Unfolding `IsConstructibleEtale` gives the affine finite-stratification criterion. -/
theorem isConstructibleEtale_iff
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology D → Sheaf Y.smallEtaleTopology D)
    (locallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology D → Prop)
    (F : Sheaf X.smallEtaleTopology D) :
    IsConstructibleEtale restrict locallyConstant F ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
          ∀ (s : Q.toSet),
            Topology.IsConstructible (s : Set U.toScheme) ∧
              let T : LocallyCloseds U.toScheme :=
                ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
              locallyConstant (restrict (Scheme.LocallyClosedReduction.ι T ≫ U.ι) F) := sorry

/-- A sheaf on a quasi-compact and quasi-separated scheme is constructible when its
restrictions to a constructible locally closed cover are constructible. -/
theorem isConstructibleEtale_of_constructible_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology D → Sheaf Y.smallEtaleTopology D)
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology D → Prop)
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology D),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F)))
    (h_finiteLocallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Sheaf Z.smallEtaleTopology D),
        finiteLocallyConstant F → finiteLocallyConstant (restrict f F))
    (h_finiteLocallyConstant_iso :
      ∀ {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology D},
        Nonempty (F ≅ G) → finiteLocallyConstant F → finiteLocallyConstant G)
    {ι : Type z} (T : ι → LocallyCloseds X)
    (hT_constructible : ∀ i, Topology.IsConstructible (T i : Set X))
    (hT_cover : ∀ x : X, ∃ i, x ∈ (T i : Set X))
    (F : Sheaf X.smallEtaleTopology D)
    (hT : ∀ i,
      IsConstructibleEtale (fun {Y} f ↦ restrict f) finiteLocallyConstant
        (restrict (Scheme.LocallyClosedReduction.ι (T i)) F)) :
    IsConstructibleEtale (fun {Y} f ↦ restrict f) finiteLocallyConstant F := sorry

/-- For a quasi-compact and quasi-separated scheme, a relative étale constructibility predicate is
equivalent to constructibility on an open cover and to a finite constructible locally closed
stratification with the supplied local-constancy predicate. -/
theorem isConstructibleEtale_tfae
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology D → Sheaf Y.smallEtaleTopology D)
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology D → Prop)
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology D),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F)))
    (h_finiteLocallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Sheaf Z.smallEtaleTopology D),
        finiteLocallyConstant F → finiteLocallyConstant (restrict f F))
    (h_finiteLocallyConstant_iso :
      ∀ {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology D},
        Nonempty (F ≅ G) → finiteLocallyConstant F → finiteLocallyConstant G)
    (F : Sheaf X.smallEtaleTopology D) :
    List.TFAE [
      IsConstructibleEtale (fun {Y} f ↦ restrict f) finiteLocallyConstant F,
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtale (fun {Y} f ↦ restrict f) finiteLocallyConstant
            (restrict (𝒰.f i) F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set X) ∧
            let T : LocallyCloseds X :=
              ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
            finiteLocallyConstant (restrict (Scheme.LocallyClosedReduction.ι T) F)] := sorry

/-- Constructibility of a sheaf on the small étale site is equivalent to constructibility
on some Zariski open cover, relative to a restriction operation compatible with composition
and a local predicate stable under restriction and invariant under isomorphisms. -/
theorem isConstructibleEtale_iff_exists_openCover
    {X : Scheme.{u}}
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology D →
        Sheaf Y.smallEtaleTopology D)
    (locallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology D → Prop)
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology D),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F)))
    (h_locallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z)
        (F : Sheaf Z.smallEtaleTopology D),
        locallyConstant F → locallyConstant (restrict f F))
    (h_locallyConstant_iso :
      ∀ {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology D},
        Nonempty (F ≅ G) → locallyConstant F → locallyConstant G)
    (F : Sheaf X.smallEtaleTopology D) :
    IsConstructibleEtale (fun {Y} f ↦ restrict f) locallyConstant F ↔
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtale (fun {Y} f ↦ restrict f) locallyConstant
            (restrict (𝒰.f i) F) := sorry

/-- A set-valued étale sheaf is constructible when its strata are finite locally constant. -/
abbrev IsConstructibleEtaleSet
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (Type (u + 1)) →
        Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : Prop :=
  IsConstructibleEtale restrict finiteLocallyConstant F

/-- An abelian-group-valued étale sheaf is constructible when its strata are finite locally
constant. -/
abbrev IsConstructibleEtaleAddCommGrp
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  IsConstructibleEtale restrict finiteLocallyConstant F

/-- For a Noetherian ring `Λ`, a module-valued étale sheaf is constructible when its strata are
locally constant of finite type. -/
abbrev IsConstructibleEtaleModule
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) : Prop :=
  IsConstructibleEtale restrict finiteTypeLocallyConstant F

/-- For a quasi-compact and quasi-separated scheme, a set-valued étale sheaf is constructible if
and only if it is constructible on an open cover and has finite locally constant restrictions on a
finite constructible locally closed stratification. -/
theorem isConstructibleEtaleSet_tfae
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    List.TFAE [
      IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) F,
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtaleSet
            (fun {Y} f ↦
              ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
                (𝒰.X i).smallEtaleTopology Y.smallEtaleTopology).obj)
            (fun {Y} G ↦ IsFiniteLocallyConstant G)
            (((Scheme.smallEtalePullback (𝒰.f i)).sheafPullback (Type (u + 1))
              X.smallEtaleTopology (𝒰.X i).smallEtaleTopology).obj F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
        ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set X) ∧
            let T : LocallyCloseds X :=
              ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
            IsFiniteLocallyConstant
              (((Scheme.smallEtalePullback (Scheme.LocallyClosedReduction.ι T)).sheafPullback
                (Type (u + 1)) X.smallEtaleTopology
                  (Scheme.LocallyClosedReduction.scheme T).smallEtaleTopology).obj F)] := sorry

/-- For a quasi-compact and quasi-separated scheme, an abelian-group-valued étale sheaf is
constructible if and only if it is constructible on an open cover and has finite locally constant
restrictions on a finite constructible locally closed stratification. -/
theorem isConstructibleEtaleAddCommGrp_tfae
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    List.TFAE [
      IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F,
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtaleAddCommGrp
            (fun {Y} f ↦
              ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
                (𝒰.X i).smallEtaleTopology Y.smallEtaleTopology).obj)
            (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G)
            (((Scheme.smallEtalePullback (𝒰.f i)).sheafPullback (AddCommGrpCat.{u + 1})
              X.smallEtaleTopology (𝒰.X i).smallEtaleTopology).obj F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
        ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set X) ∧
            let T : LocallyCloseds X :=
              ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
            IsFiniteLocallyConstantAddCommGrp
              (((Scheme.smallEtalePullback (Scheme.LocallyClosedReduction.ι T)).sheafPullback
                (AddCommGrpCat.{u + 1}) X.smallEtaleTopology
                  (Scheme.LocallyClosedReduction.scheme T).smallEtaleTopology).obj F)] := sorry

/-- For a quasi-compact and quasi-separated scheme and a Noetherian ring `Λ`, a module-valued
étale sheaf is constructible if and only if it is constructible on an open cover and has locally
constant finite-type restrictions on a finite constructible locally closed stratification. -/
theorem isConstructibleEtaleModule_tfae
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
      (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    List.TFAE [
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
          IsFiniteTypeLocallyConstantModule G) F,
      ∃ (𝒰 : X.OpenCover),
        ∀ i : 𝒰.I₀,
          IsConstructibleEtaleModule
            (fun {Y} f ↦
              ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
                (𝒰.X i).smallEtaleTopology Y.smallEtaleTopology).obj)
            (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
              IsFiniteTypeLocallyConstantModule G)
            (((Scheme.smallEtalePullback (𝒰.f i)).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology (𝒰.X i).smallEtaleTopology).obj F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
        ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set X) ∧
            let T : LocallyCloseds X :=
              ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
            IsFiniteTypeLocallyConstantModule
              (((Scheme.smallEtalePullback (Scheme.LocallyClosedReduction.ι T)).sheafPullback
                (ModuleCat.{w} Λ) X.smallEtaleTopology
                  (Scheme.LocallyClosedReduction.scheme T).smallEtaleTopology).obj F)] := sorry

end CategoryTheory.Sheaf
