/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.OverAbelian

/-!
# Structure sheaf and modules on the small étale site of an algebraic space

The structure sheaf assigns to an étale chart its ring of global sections. Module sheaves
are sheaves of modules over this ring sheaf on the small étale topology.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism map of `smallEtaleToScheme X` is the underlying morphism of schemes. -/
theorem smallEtaleToScheme_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (f : U ⟶ V) : (smallEtaleToScheme X).map f = f.left.left :=
  sorry

/-- The ring presheaf on the small étale site of `X` with value `Γ(U, 𝒪_U)`. -/
abbrev structurePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u} :=
  (smallEtaleToScheme X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The value of `structurePresheaf X` at `U` is the global-sections ring of the underlying
scheme. -/
theorem structurePresheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (structurePresheaf X).obj (op U) = RingCat.of Γ(U.left.left, ⊤) :=
  sorry

/-- Restriction in `structurePresheaf X` is the map on global sections induced by the
underlying morphism of schemes. -/
theorem structurePresheaf_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (g : U ⟶ V) :
    (structurePresheaf X).map g.op =
      RingCat.ofHom ((smallEtaleToScheme X).map g).appTop.hom :=
  sorry

/-- The global-sections presheaf on the small étale site of an algebraic space is a sheaf. -/
theorem structurePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (smallEtaleTopology X) (structurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪_X` on the small étale site of an algebraic space. -/
def structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

/-- On a scheme étale over `X`, the structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (structureSheaf X).obj.obj (op U) = RingCat.of Γ(U.left.left, ⊤) :=
  sorry

/-- The category of sheaves of modules on the ringed site `(X_étale, 𝒪_X)`. -/
abbrev Modules {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  SheafOfModules.{u} (structureSheaf X)

/-- The module category of `X` is the category of sheaves of modules over `𝒪_X`. -/
theorem Modules_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Modules X = SheafOfModules.{u} (structureSheaf X) :=
  rfl

/-- Abelian-group-valued sheaf composition exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasSheafCompose {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasWeakSheafify_addCommGrp {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
  smallEtaleAbelianSheafification X

/-- On the small étale topology of an algebraic space, sheafification equivalences are the
locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of the small étale topology of
an algebraic space. -/
instance smallEtaleTopology_over_hasSheafCompose {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : smallEtaleSite X,
      ((smallEtaleTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on every slice of the small étale topology of
an algebraic space. -/
instance smallEtaleTopology_over_hasWeakSheafify {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : smallEtaleSite X,
      HasWeakSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u} :=
  fun U ↦ smallEtaleOverAbelianSheafification X U

/-- On every slice of the small étale topology of an algebraic space, sheafification
equivalences are the locally bijective morphisms. -/
instance smallEtaleTopology_over_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : smallEtaleSite X,
      ((smallEtaleTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Sheafification of abelian-group-valued presheaves on the small étale site of
an algebraic space is left exact. -/
instance smallEtaleTopology_hasSheafify_addCommGrp {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u} where
  isRightAdjoint := inferInstance
  isLeftExact := sorry

end AlgebraicGeometry.AlgebraicSpace
