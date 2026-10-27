/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Openness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.OpenSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces.AffineCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.Cofiltered
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.Lift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism

/-!
# Vanishing locus of a local section of an abelian spaces-étale sheaf

A local section of an abelian sheaf on `X_spaces,étale` vanishes on a unique largest
open of `|U|`, compared with open subspaces, étale images, and geometric germs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The inclusion of an open subspace of an étale algebraic space over `X`, postcomposed with
the structure morphism, is étale. -/
theorem etale_openSubspace_comp (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    Etale (W.ι ≫ U.hom) := by
  constructor
  intro T φ hφ
  exact U.prop.of_etale (φ ≫ W.ι) ((OpenSubspace.etale_ι W).of_etale φ hφ)

/-- The object of `X_spaces,étale` associated to an open subspace of an étale object `U`. -/
def openSubspaceSite (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (W.ι ≫ U.hom) (etale_openSubspace_comp U W)

/-- The structure morphism of `openSubspaceSite U W` is `W.ι ≫ U.hom`. -/
theorem openSubspaceSite_hom (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    (openSubspaceSite U W).hom = W.ι ≫ U.hom :=
  rfl

/-- The underlying algebraic space of `openSubspaceSite U W` is `W`. -/
theorem openSubspaceSite_left (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    (openSubspaceSite U W).left = W.X :=
  rfl

/-- The restriction arrow `W ⟶ U` in `X_spaces,étale` associated to an open subspace of `U`. -/
def openSubspaceHom (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    openSubspaceSite U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl

/-- The underlying morphism of algebraic spaces of `openSubspaceHom U W` is `W.ι`. -/
theorem openSubspaceHom_left (U : spacesEtaleSite X) (W : OpenSubspace U.left) :
    (openSubspaceHom U W).left = W.ι :=
  rfl

private theorem exists_openSubspaceHom_lift (U : spacesEtaleSite X)
    (W : OpenSubspace U.left) {V : spacesEtaleSite X} (φ : V ⟶ U)
    (h : Set.range (Points.map φ.left) ⊆ W.pointsSet) :
    ∃ ψ : V ⟶ openSubspaceSite U W, ψ ≫ openSubspaceHom U W = φ := by
  obtain ⟨g, hg⟩ := (W.exists_lift_iff_range_subset φ.left).mpr h
  refine ⟨MorphismProperty.Over.homMk g ?_, MorphismProperty.Over.Hom.ext hg⟩
  change g ≫ (W.ι ≫ U.hom) = V.hom
  calc
    g ≫ (W.ι ≫ U.hom) = (g ≫ W.ι) ≫ U.hom := (Category.assoc _ _ _).symm
    _ = φ.left ≫ U.hom := congrArg (fun k ↦ k ≫ U.hom) hg
    _ = V.hom := MorphismProperty.Over.w φ

/-- Restriction of a local section of an abelian sheaf along a morphism of `X_spaces,étale`. -/
def sectionRestrict (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U V : spacesEtaleSite X} (φ : V ⟶ U) (σ : F.obj.obj (op U)) : F.obj.obj (op V) :=
  F.obj.map φ.op σ

/-- Restriction of a local section is the underlying presheaf action. -/
theorem sectionRestrict_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U V : spacesEtaleSite X} (φ : V ⟶ U) (σ : F.obj.obj (op U)) :
    sectionRestrict F φ σ = F.obj.map φ.op σ :=
  rfl

private theorem sectionRestrict_comp
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U V W : spacesEtaleSite X} (φ : V ⟶ U) (ψ : W ⟶ V) (σ : F.obj.obj (op U)) :
    sectionRestrict F ψ (sectionRestrict F φ σ) = sectionRestrict F (ψ ≫ φ) σ := by
  change (F.obj.map ψ.op) ((F.obj.map φ.op) σ) = (F.obj.map (ψ ≫ φ).op) σ
  rw [op_comp, F.obj.map_comp]
  rfl

private theorem section_ext_of_point_cover
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U : spacesEtaleSite X} {I : Type u} (V : I → spacesEtaleSite X)
    (f : ∀ i, V i ⟶ U)
    (hcover : ⋃ i, Set.range (Points.map (f i).left) = Set.univ)
    (σ τ : F.obj.obj (op U))
    (h : ∀ i, sectionRestrict F (f i) σ = sectionRestrict F (f i) τ) : σ = τ := by
  have hmem : Presieve.ofArrows V f ∈ spacesEtalePrecoverage X U :=
    ⟨I, inferInstance, V, f, rfl, hcover⟩
  apply F.isSeparated U (Sieve.ofArrows V f)
    ((spacesEtalePrecoverage X).generate_mem_toGrothendieck hmem) σ τ
  rintro Y g ⟨Z, k, _, ⟨i⟩, rfl⟩
  change sectionRestrict F (k ≫ f i) σ = sectionRestrict F (k ≫ f i) τ
  rw [← sectionRestrict_comp, ← sectionRestrict_comp, h i]

private theorem sectionRestrict_injective_of_points_surjective
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    {U V : spacesEtaleSite X} (φ : V ⟶ U)
    (hφ : Function.Surjective (Points.map φ.left)) :
    Function.Injective (sectionRestrict F φ) := by
  intro σ τ h
  apply section_ext_of_point_cover F (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ φ) ?_
    σ τ (fun _ ↦ h)
  simpa only [Set.iUnion_const] using Set.range_eq_univ.mpr hφ

/-- The largest open of `|U|` on which a local section of an abelian sheaf vanishes, as a
subset of points. -/
def sectionVanishingSet (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) : Set (Points U.left) :=
  {x | ∃ W : OpenSubspace U.left,
      x ∈ W.pointsSet ∧ sectionRestrict F (openSubspaceHom U W) σ = 0}

/-- A point of `|U|` lies in `sectionVanishingSet F U σ` if and only if it lies in some open
subspace of `U` on which `σ` restricts to zero. -/
theorem mem_sectionVanishingSet_iff (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (x : Points U.left) :
    x ∈ sectionVanishingSet F U σ ↔
      ∃ W : OpenSubspace U.left,
        x ∈ W.pointsSet ∧ sectionRestrict F (openSubspaceHom U W) σ = 0 :=
  Iff.rfl

/-- The vanishing locus of a local section is open in `|U|`. -/
theorem isOpen_sectionVanishingSet (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) :
    IsOpen (sectionVanishingSet F U σ) := by
  have hset : sectionVanishingSet F U σ =
      ⋃ (W : OpenSubspace U.left)
        (_ : sectionRestrict F (openSubspaceHom U W) σ = 0), W.pointsSet := by
    ext x
    simp only [sectionVanishingSet, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact exists_congr (fun W ↦ and_comm)
  rw [hset]
  exact isOpen_iUnion fun W ↦ isOpen_iUnion fun _ ↦ W.isOpen_pointsSet

/-- The vanishing locus of a local section is the point-set of some open subspace of `U`. -/
theorem exists_openSubspace_sectionVanishingSet
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) :
    ∃ W : OpenSubspace U.left, W.pointsSet = sectionVanishingSet F U σ := by
  refine ⟨OpenSubspace.fromOpens ⟨_, isOpen_sectionVanishingSet F U σ⟩, ?_⟩
  exact OpenSubspace.fromOpens_pointsSet _

/-- The underlying type-valued presheaf of an abelian sheaf on `X_spaces,étale`. -/
def typePresheaf (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1) :=
  F.obj ⋙ forget AddCommGrpCat.{u + 1}

/-- The type-valued presheaf of an abelian sheaf is the forgetful image of its underlying
presheaf. -/
theorem typePresheaf_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    typePresheaf F = F.obj ⋙ forget AddCommGrpCat.{u + 1} :=
  rfl

/-- The étale neighborhood `(U, ū)` of the geometric point `x̄ = (U ⟶ X) ∘ ū`. -/
def neighborhoodOf (U : spacesEtaleSite X) (ubar : GeometricPoint U.left) :
    GeometricPoint.EtaleNeighborhood (ubar.map U.hom) :=
  GeometricPoint.EtaleNeighborhood.of U ubar.hom rfl

/-- The underlying spaces-étale object of `neighborhoodOf U ubar` is `U`. -/
theorem neighborhoodOf_toSpacesEtale (U : spacesEtaleSite X)
    (ubar : GeometricPoint U.left) :
    (neighborhoodOf U ubar).toSpacesEtale = U :=
  rfl

/-- The germ of a local section at a geometric point of `U`, as an element of the spaces-étale
stalk at `x̄ = ubar.map U.hom`. -/
def sectionGerm (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left) :
    GeometricPoint.spacesEtaleStalk (ubar.map U.hom) (typePresheaf F) :=
  GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) σ

/-- The germ of a local section is the spaces-étale colimit inclusion of that section. -/
theorem sectionGerm_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left) :
    sectionGerm F U σ ubar =
      GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) σ :=
  rfl

/-- The zero germ of an abelian sheaf at a geometric point of `U`. -/
def sectionGerm_zero (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (ubar : GeometricPoint U.left) :
    GeometricPoint.spacesEtaleStalk (ubar.map U.hom) (typePresheaf F) :=
  GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) (0 : F.obj.obj (op U))

/-- The zero germ is the spaces-étale colimit inclusion of the zero section. -/
theorem sectionGerm_zero_eq (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (ubar : GeometricPoint U.left) :
    sectionGerm_zero F U ubar =
      GeometricPoint.toSpacesEtaleStalk (neighborhoodOf U ubar) (0 : F.obj.obj (op U)) :=
  rfl

/-- `sectionVanishingSet F U σ` is the largest open of `|U|` on which the
local section `σ` restricts to `0`. Equivalently, restriction of `σ` to an open subspace
`W ⊂ U` vanishes if and only if `W.pointsSet ⊆ sectionVanishingSet F U σ`. -/
@[stacks 04K9]
theorem sectionRestrict_eq_zero_iff_pointsSet_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (W : OpenSubspace U.left) :
    sectionRestrict F (openSubspaceHom U W) σ = 0 ↔
      W.pointsSet ⊆ sectionVanishingSet F U σ := by
  constructor
  · intro h x hx
    exact ⟨W, hx, h⟩
  · intro h
    classical
    -- Scheme points give a `Type u` index for the open cover.
    let T := AtlasInput.scheme W.X
    let a : T.left → Points W.X := Points.mapOfOver (AtlasInput.map W.X)
    have ha : Function.Surjective a :=
      (Points.isOpenQuotientMap_mapOfOver (AtlasInput.map W.X)
        (AtlasInput.representableEtale W.X) (AtlasInput.locallySurjective W.X)).surjective
    have hlocal : ∀ t : T.left, ∃ Z : OpenSubspace U.left,
        Points.map W.ι (a t) ∈ Z.pointsSet ∧
          sectionRestrict F (openSubspaceHom U Z) σ = 0 :=
      fun t ↦ h ⟨a t, rfl⟩
    choose Z hZ hzero using hlocal
    let V : T.left → OpenSubspace W.X := fun t ↦ (Z t).inverseImage W.ι
    let V' : T.left → spacesEtaleSite X := fun t ↦
      openSubspaceSite (openSubspaceSite U W) (V t)
    let f : ∀ t, V' t ⟶ openSubspaceSite U W := fun t ↦
      openSubspaceHom (openSubspaceSite U W) (V t)
    have hcover : ⋃ t, Set.range (Points.map (f t).left) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro w
      obtain ⟨t, rfl⟩ := ha w
      apply Set.mem_iUnion.mpr
      refine ⟨t, ?_⟩
      change a t ∈ ((Z t).inverseImage W.ι).pointsSet
      rw [OpenSubspace.inverseImage_pointsSet]
      exact hZ t
    apply section_ext_of_point_cover F V' f hcover
      (sectionRestrict F (openSubspaceHom U W) σ) 0
    intro t
    have hrange : Set.range (Points.map (f t ≫ openSubspaceHom U W).left) ⊆
        (Z t).pointsSet := by
      rintro _ ⟨v, rfl⟩
      change Points.map ((V t).ι ≫ W.ι) v ∈ (Z t).pointsSet
      rw [Points.map_comp]
      have hv : Points.map (V t).ι v ∈ ((Z t).inverseImage W.ι).pointsSet :=
        ⟨v, rfl⟩
      rw [OpenSubspace.inverseImage_pointsSet] at hv
      exact hv
    obtain ⟨g, hg⟩ := exists_openSubspaceHom_lift U (Z t)
      (f t ≫ openSubspaceHom U W) hrange
    calc
      sectionRestrict F (f t) (sectionRestrict F (openSubspaceHom U W) σ) =
          sectionRestrict F (f t ≫ openSubspaceHom U W) σ := sectionRestrict_comp _ _ _ _
      _ = sectionRestrict F (g ≫ openSubspaceHom U (Z t)) σ :=
        congrArg (fun k ↦ sectionRestrict F k σ) hg.symm
      _ = sectionRestrict F g (sectionRestrict F (openSubspaceHom U (Z t)) σ) :=
        (sectionRestrict_comp _ _ _ _).symm
      _ = sectionRestrict F g 0 := congrArg (sectionRestrict F g) (hzero t)
      _ = 0 := (F.obj.map g.op).hom.map_zero
      _ = sectionRestrict F (f t) 0 := (F.obj.map (f t).op).hom.map_zero.symm

/-- For every morphism `φ : V ⟶ U` in `X_spaces,étale`, the restriction
`σ |_ V` vanishes if and only if the image `φ(V) ⊂ |U|` is contained in
`sectionVanishingSet F U σ`. -/
@[stacks 04K9]
theorem sectionRestrict_eq_zero_iff_range_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) {V : spacesEtaleSite X} (φ : V ⟶ U) :
    sectionRestrict F φ σ = 0 ↔
      Set.range (Points.map φ.left) ⊆ sectionVanishingSet F U σ := by
  constructor
  · intro hφ
    let W := OpenSubspace.fromOpens
      ⟨Set.range (Points.map φ.left), (Etale.isOpenMap φ.left).isOpen_range⟩
    have hW : W.pointsSet = Set.range (Points.map φ.left) :=
      OpenSubspace.fromOpens_pointsSet _
    obtain ⟨ψ, hψ⟩ := exists_openSubspaceHom_lift U W φ (by rw [hW])
    have hleft : ψ.left ≫ W.ι = φ.left :=
      congrArg (fun f : V ⟶ U ↦ f.left) hψ
    have hsurj : Function.Surjective (Points.map ψ.left) := by
      letI : Mono W.ι := (OpenSubspace.spec W).2
      intro w
      obtain ⟨v, hv⟩ := hW ▸ (show Points.map W.ι w ∈ W.pointsSet from ⟨w, rfl⟩)
      refine ⟨v, Points.map_injective_of_mono W.ι ?_⟩
      calc
        Points.map W.ι (Points.map ψ.left v) = Points.map (ψ.left ≫ W.ι) v :=
          (Points.map_comp ψ.left W.ι v).symm
        _ = Points.map φ.left v := congrArg (fun k ↦ Points.map k v) hleft
        _ = Points.map W.ι w := hv
    have hzero : sectionRestrict F (openSubspaceHom U W) σ = 0 := by
      apply sectionRestrict_injective_of_points_surjective F ψ hsurj
      calc
        sectionRestrict F ψ (sectionRestrict F (openSubspaceHom U W) σ) =
          sectionRestrict F φ σ := by rw [sectionRestrict_comp, hψ]
        _ = 0 := hφ
        _ = sectionRestrict F ψ 0 := (F.obj.map ψ.op).hom.map_zero.symm
    intro x hx
    exact ⟨W, hW.symm ▸ hx, hzero⟩
  · intro h
    obtain ⟨W, hW⟩ := exists_openSubspace_sectionVanishingSet F U σ
    have hzero : sectionRestrict F (openSubspaceHom U W) σ = 0 :=
      (sectionRestrict_eq_zero_iff_pointsSet_subset F U σ W).mpr (by rw [hW])
    obtain ⟨ψ, hψ⟩ := exists_openSubspaceHom_lift U W φ (by rw [hW]; exact h)
    calc
      sectionRestrict F φ σ =
        sectionRestrict F ψ (sectionRestrict F (openSubspaceHom U W) σ) := by
          rw [sectionRestrict_comp, hψ]
      _ = sectionRestrict F ψ 0 := congrArg (sectionRestrict F ψ) hzero
      _ = 0 := (F.obj.map ψ.op).hom.map_zero

/-- For every geometric point `ū` of `U`, the germ `(U, ū, σ)` vanishes
in `F_x̄` if and only if `ū` lies in `sectionVanishingSet F U σ`, where
`x̄ = (U ⟶ X) ∘ ū`. -/
@[stacks 04K9]
theorem sectionGerm_eq_zero_iff_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left) :
    sectionGerm F U σ ubar = sectionGerm_zero F U ubar ↔
      ubar.image ∈ sectionVanishingSet F U σ := by
  let D := GeometricPoint.spacesSectionsDiagram (ubar.map U.hom) (typePresheaf F)
  change D.ιColimitType (op (neighborhoodOf U ubar)) σ =
    D.ιColimitType (op (neighborhoodOf U ubar)) (0 : F.obj.obj (op U)) ↔ _
  rw [D.ιColimitType_eq_iff,
    ← Limits.Types.FilteredColimit.rel_eq_eqvGen_colimitTypeRel]
  constructor
  · rintro ⟨N, f, g, h⟩
    have hzero : sectionRestrict F f.unop.val σ = 0 := by
      change (F.obj.map f.unop.val.op) σ = 0
      change (F.obj.map f.unop.val.op) σ = (F.obj.map g.unop.val.op) 0 at h
      exact h.trans (F.obj.map g.unop.val.op).hom.map_zero
    apply (sectionRestrict_eq_zero_iff_range_subset F U σ f.unop.val).mp hzero
    refine ⟨N.unop.geometricPoint.image, ?_⟩
    have hfac := GeometricPoint.EtaleNeighborhood.Hom.lift_fac f.unop
    change N.unop.lift ≫ f.unop.val.left = ubar.hom at hfac
    change Points.mk (FieldValuedPoint.of ubar.K ubar.structureHom
        (N.unop.lift ≫ f.unop.val.left)) =
      Points.mk (FieldValuedPoint.of ubar.K ubar.structureHom ubar.hom)
    exact congrArg
      (fun k ↦ Points.mk (FieldValuedPoint.of ubar.K ubar.structureHom k)) hfac
  · rintro ⟨W, hx, hσ⟩
    obtain ⟨p, hp⟩ := hx
    letI : Etale W.ι := OpenSubspace.etale_ι W
    obtain ⟨l, hl, _⟩ := GeometricPoint.exists_liftHom_of_etale
      ubar ubar.image rfl W.ι p hp
    let N : GeometricPoint.EtaleNeighborhood (ubar.map U.hom) :=
      GeometricPoint.EtaleNeighborhood.of (openSubspaceSite U W) l (by
        change l ≫ (W.ι ≫ U.hom) = ubar.hom ≫ U.hom
        rw [← Category.assoc, hl]
        rfl)
    let f : N ⟶ neighborhoodOf U ubar :=
      GeometricPoint.EtaleNeighborhood.Hom.of (openSubspaceHom U W) hl
    refine ⟨op N, f.op, f.op, ?_⟩
    change sectionRestrict F (openSubspaceHom U W) σ =
      (F.obj.map (openSubspaceHom U W).op) 0
    rw [hσ]
    exact (F.obj.map (openSubspaceHom U W).op).hom.map_zero.symm

end AlgebraicGeometry.AlgebraicSpace
