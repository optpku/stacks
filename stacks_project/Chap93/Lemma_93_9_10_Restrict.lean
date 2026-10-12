/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap93.Lemma_93_9_6_Restrict
public import stacks_project.Chap93.Lemma_93_9_7_GlobalSections
public import stacks_project.Chap93.Situation_93_9_9_Deformation

/-!
# Ring-restriction functors along a two-chart affine overlap

The cospan legs `Def_{P₁} ⥤ᵇ Def_{P₁₂}` and `Def_{P₂} ⥤ᵇ Def_{P₁₂}` send a
deformation of `Γ(X, Uᵢ)` to the global sections of the corresponding open of
`U₁ ⊓ U₂`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The structure morphism `Spec Q ⟶ Spec A` of a flat algebra pair. -/
def specStructureHomOf (Y : FlatAlgebraCat Λ k) :
    Spec (CommRingCat.of Y.algebra) ⟶ Spec (CommRingCat.of Y.base.carrier) :=
  Spec.map (CommRingCat.ofHom (algebraMap Y.base.carrier Y.algebra))

/-- `Spec.map` of a flat algebra map is a flat morphism of schemes. -/
instance instFlat_specStructureHomOf (Y : FlatAlgebraCat Λ k) :
    AlgebraicGeometry.Flat (specStructureHomOf Y) :=
  sorry

/-- The affine scheme pair `(A, Spec Q)` attached to a flat algebra pair `(A, Q)`. -/
def specPairOf (Y : FlatAlgebraCat Λ k) : FlatSchemeCat Λ k :=
  of Y.base (Spec (CommRingCat.of Y.algebra)) (specStructureHomOf Y)

/-- `specPairOf` keeps the stored Artinian base. -/
theorem specPairOf_base (Y : FlatAlgebraCat Λ k) : (specPairOf Y).base = Y.base :=
  sorry

/-- The scheme morphism attached to a morphism of flat algebra pairs. -/
def specPairMap {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P) : specPairOf Q ⟶ specPairOf P :=
  Hom.of f.baseHom (Spec.map (CommRingCat.ofHom f.toRingHom)) sorry

/-- `specPairMap` preserves the underlying morphism of Artinian local algebras. -/
theorem specPairMap_baseHom {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P) :
    (specPairMap f).baseHom = f.baseHom :=
  sorry

variable (Λ k) (P : Type u) [CommRing P] [Algebra k P]

/-- The residue morphism `(A, Spec Q) ⟶ (k, Spec P)` of a deformation of `P`. -/
def specResidueHom (ξ : FlatAlgebraCat.deformationCategory Λ k P) :
    specPairOf ξ.left ⟶ ofResidue Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) :=
  Hom.of ξ.hom.baseHom (Spec.map (CommRingCat.ofHom ξ.hom.toRingHom)) sorry

/-- The ordinary functor `Def_P ⥤ Def_{Spec P}` sending `(A, Q)` to `(A, Spec Q)`. -/
def specFunctor :
    FlatAlgebraCat.deformationCategory Λ k P ⥤
      deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) where
  obj ξ := Over.mk (specResidueHom Λ k P ξ)
  map φ := Over.homMk (specPairMap φ.left) sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `specFunctor` keep the stored Artinian base. -/
theorem specFunctor_obj_left_base (ξ : FlatAlgebraCat.deformationCategory Λ k P) :
    ((specFunctor Λ k P).obj ξ).left.base = ξ.left.base :=
  sorry

/-- `specFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem specFunctor_comp_forget :
    specFunctor Λ k P ⋙ schemeDeformationForget Λ k P = algebraDeformationForget Λ k P :=
  sorry

/-- The based functor `Def_P ⥤ᵇ Def_{Spec P}` sending `(A, Q)` to `(A, Spec Q)`. -/
def specBasedFunctor :
    BasedCategory.ofFunctor (algebraDeformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (schemeDeformationForget Λ k P) :=
  BasedFunctor.ofFunctor (specFunctor Λ k P) (specFunctor_comp_forget Λ k P)

/-- The underlying ordinary functor of `specBasedFunctor` is `specFunctor`. -/
theorem specBasedFunctor_toFunctor :
    (specBasedFunctor Λ k P).toFunctor = specFunctor Λ k P :=
  sorry

end FlatSchemeCat

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {X : Scheme.{u}}

/-- The open of `Spec Γ(X, U₁)` corresponding to `U₁ ⊓ U₂`. -/
abbrev overlapOpenSpec₁ (c : TwoAffineOpenCover X) : (Spec Γ(X, c.U₁)).Opens :=
  c.fromSpec₁ ⁻¹ᵁ (c.U₁ ⊓ c.U₂)

/-- The open of `Spec Γ(X, U₂)` corresponding to `U₁ ⊓ U₂`. -/
abbrev overlapOpenSpec₂ (c : TwoAffineOpenCover X) : (Spec Γ(X, c.U₂)).Opens :=
  c.fromSpec₂ ⁻¹ᵁ (c.U₁ ⊓ c.U₂)

/-- `fromSpec₁` is an open immersion. -/
instance instIsOpenImmersion_fromSpec₁ (c : TwoAffineOpenCover X) :
    IsOpenImmersion c.fromSpec₁ :=
  inferInstanceAs (IsOpenImmersion c.isAffine_U₁.fromSpec)

/-- `fromSpec₂` is an open immersion. -/
instance instIsOpenImmersion_fromSpec₂ (c : TwoAffineOpenCover X) :
    IsOpenImmersion c.fromSpec₂ :=
  inferInstanceAs (IsOpenImmersion c.isAffine_U₂.fromSpec)

/-- The composite open immersion of the first overlap open into `X`. -/
instance instIsOpenImmersion_overlapOpenSpec₁_ι_fromSpec (c : TwoAffineOpenCover X) :
    IsOpenImmersion ((overlapOpenSpec₁ c).ι ≫ c.fromSpec₁) :=
  IsOpenImmersion.comp (overlapOpenSpec₁ c).ι c.fromSpec₁

/-- The composite open immersion of the second overlap open into `X`. -/
instance instIsOpenImmersion_overlapOpenSpec₂_ι_fromSpec (c : TwoAffineOpenCover X) :
    IsOpenImmersion ((overlapOpenSpec₂ c).ι ≫ c.fromSpec₂) :=
  IsOpenImmersion.comp (overlapOpenSpec₂ c).ι c.fromSpec₂

/-- The overlap open of `Spec Γ(X, U₁)` is isomorphic to `U₁ ⊓ U₂` over `X`. -/
def overlapIso₁ (c : TwoAffineOpenCover X) :
    (overlapOpenSpec₁ c).toScheme ≅ (c.U₁ ⊓ c.U₂).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((overlapOpenSpec₁ c).ι ≫ c.fromSpec₁) (c.U₁ ⊓ c.U₂).ι <| by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    exact congr_arg (SetLike.coe : X.Opens → Set X)
      ((c.fromSpec₁.image_preimage_eq_opensRange_inf (c.U₁ ⊓ c.U₂)).trans
        (by dsimp [fromSpec₁]; simp [IsAffineOpen.opensRange_fromSpec]))

/-- The overlap open of `Spec Γ(X, U₂)` is isomorphic to `U₁ ⊓ U₂` over `X`. -/
def overlapIso₂ (c : TwoAffineOpenCover X) :
    (overlapOpenSpec₂ c).toScheme ≅ (c.U₁ ⊓ c.U₂).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((overlapOpenSpec₂ c).ι ≫ c.fromSpec₂) (c.U₁ ⊓ c.U₂).ι <| by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    exact congr_arg (SetLike.coe : X.Opens → Set X)
      ((c.fromSpec₂.image_preimage_eq_opensRange_inf (c.U₁ ⊓ c.U₂)).trans
        (by dsimp [fromSpec₂]; simp [IsAffineOpen.opensRange_fromSpec]))

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))

/-- The structure morphism of `Spec P₁` over `k`. -/
def specStructureHom₁ :
    Spec (CommRingCat.of (ring₁ c)) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₁ Λ k c hX
  FlatSchemeCat.specStructureHom Λ k (ring₁ c)

/-- The structure morphism of `Spec P₁` over `k` is flat. -/
instance instFlat_specStructureHom₁ : AlgebraicGeometry.Flat (specStructureHom₁ Λ k c hX) :=
  sorry

/-- The structure morphism of `Spec P₂` over `k`. -/
def specStructureHom₂ :
    Spec (CommRingCat.of (ring₂ c)) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₂ Λ k c hX
  FlatSchemeCat.specStructureHom Λ k (ring₂ c)

/-- The structure morphism of `Spec P₂` over `k` is flat. -/
instance instFlat_specStructureHom₂ : AlgebraicGeometry.Flat (specStructureHom₂ Λ k c hX) :=
  sorry

/-- The deformation category of `Spec P₁`. -/
abbrev deformationCategory_spec₁ :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₁ Λ k c hX
  FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (ring₁ c)))
    (specStructureHom₁ Λ k c hX)

/-- The deformation category of `Spec P₂`. -/
abbrev deformationCategory_spec₂ :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₂ Λ k c hX
  FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (ring₂ c)))
    (specStructureHom₂ Λ k c hX)

/-- The deformation category of the first overlap open of `Spec P₁`. -/
abbrev deformationCategory_overlap₁ :=
  FlatSchemeCat.deformationCategory Λ k (overlapOpenSpec₁ c).toScheme
    ((overlapOpenSpec₁ c).ι ≫ specStructureHom₁ Λ k c hX)

/-- The deformation category of the second overlap open of `Spec P₂`. -/
abbrev deformationCategory_overlap₂ :=
  FlatSchemeCat.deformationCategory Λ k (overlapOpenSpec₂ c).toScheme
    ((overlapOpenSpec₂ c).ι ≫ specStructureHom₂ Λ k c hX)

/-- The ordinary functor `Def_{P₁} ⥤ Def_{Spec P₁}`. -/
def specFunctor₁ : deformationCategory_ring₁ Λ k c hX ⥤ deformationCategory_spec₁ Λ k c hX :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₁ Λ k c hX
  FlatSchemeCat.specFunctor Λ k (ring₁ c)

/-- The ordinary functor `Def_{P₂} ⥤ Def_{Spec P₂}`. -/
def specFunctor₂ : deformationCategory_ring₂ Λ k c hX ⥤ deformationCategory_spec₂ Λ k c hX :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₂ Λ k c hX
  FlatSchemeCat.specFunctor Λ k (ring₂ c)

/-- The `A`-algebra of global sections of a deformation of `overlapOpenSpec₁`. -/
def overlapSectionsObj₁ (Y : deformationCategory_overlap₁ Λ k c hX) : FlatAlgebraCat Λ k where
  base := Y.left.base
  algebra := (Γ(Y.left.scheme, ⊤) : Type u)
  isAlgebra := FlatSchemeCat.algebraOfStructureHom Y.left
  isFlat := sorry

/-- The ring map `Γ(W, ⊤) →+* P₁₂` of a deformation of the first overlap open. -/
def overlapSectionsRingHom₁ (Y : deformationCategory_overlap₁ Λ k c hX) :
    Γ(Y.left.scheme, ⊤) →+* Γ(X, c.U₁ ⊓ c.U₂) :=
  (Y.hom.schemeHom.appTop ≫ (overlapIso₁ c).inv.appTop ≫ (c.U₁ ⊓ c.U₂).topIso.hom).hom

/-- The residue object `(k, P₁₂)`. -/
abbrev ofResidue_ringInf : FlatAlgebraCat Λ k :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁ ⊓ U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRingInf Λ k c hX
  FlatAlgebraCat.ofResidue Λ k (ringInf c)

/-- The slice projection of `Def_{P₁}` to `C_Λ`. -/
abbrev algebraForget_ring₁ : deformationCategory_ring₁ Λ k c hX ⥤ ArtinianLocalAlgCat Λ k :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₁ Λ k c hX
  FlatSchemeCat.algebraDeformationForget Λ k (ring₁ c)

/-- The slice projection of `Def_{P₂}` to `C_Λ`. -/
abbrev algebraForget_ring₂ : deformationCategory_ring₂ Λ k c hX ⥤ ArtinianLocalAlgCat Λ k :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₂ Λ k c hX
  FlatSchemeCat.algebraDeformationForget Λ k (ring₂ c)

/-- The slice projection of `Def_{P₁₂}` to `C_Λ`. -/
abbrev algebraForget_ringInf : deformationCategory_ringInf Λ k c hX ⥤ ArtinianLocalAlgCat Λ k :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁ ⊓ U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRingInf Λ k c hX
  FlatSchemeCat.algebraDeformationForget Λ k (ringInf c)

/-- The morphism `(A, Γ(W, ⊤)) ⟶ (k, P₁₂)` induced by a deformation of `overlapOpenSpec₁`. -/
def overlapSectionsResidueHom₁ (Y : deformationCategory_overlap₁ Λ k c hX) :
    overlapSectionsObj₁ Λ k c hX Y ⟶ ofResidue_ringInf Λ k c hX :=
  FlatAlgebraCat.Hom.of Y.hom.baseHom (overlapSectionsRingHom₁ Λ k c hX Y) sorry sorry

/-- A morphism of deformations of `overlapOpenSpec₁` induces the map on global sections. -/
def overlapSectionsMap₁ {src tgt : deformationCategory_overlap₁ Λ k c hX} (f : src ⟶ tgt) :
    overlapSectionsObj₁ Λ k c hX src ⟶ overlapSectionsObj₁ Λ k c hX tgt :=
  FlatAlgebraCat.Hom.of f.left.baseHom f.left.schemeHom.appTop.hom sorry sorry

/-- The functor `Def_{overlapOpenSpec₁} ⥤ Def_{P₁₂}` sending `(A, W)` to `(A, Γ(W, ⊤))`. -/
def overlapSectionsFunctor₁ :
    deformationCategory_overlap₁ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX where
  obj Y := Over.mk (overlapSectionsResidueHom₁ Λ k c hX Y)
  map f := Over.homMk (overlapSectionsMap₁ Λ k c hX f) sorry
  map_id := sorry
  map_comp := sorry

/-- The ordinary functor `Def_{P₁} ⥤ Def_{P₁₂}` of restriction along `U₁₂ ⊂ U₁`. -/
def restrictRingFunctor₁ :
    deformationCategory_ring₁ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX :=
  (specFunctor₁ Λ k c hX).comp
    ((FlatSchemeCat.restrictFunctor Λ k (Spec (CommRingCat.of (ring₁ c)))
        (specStructureHom₁ Λ k c hX) (overlapOpenSpec₁ c)).comp
      (overlapSectionsFunctor₁ Λ k c hX))

/-- `restrictRingFunctor₁` lies strictly over `ArtinianLocalAlgCat`. -/
theorem restrictRingFunctor₁_comp_forget :
    (restrictRingFunctor₁ Λ k c hX).comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₁ Λ k c hX :=
  sorry

/-- The morphism `Def_{P₁} ⥤ᵇ Def_{P₁₂}` of categories over `ArtinianLocalAlgCat`. -/
def restrictRing₁ :
    BasedCategory.ofFunctor (algebraForget_ring₁ Λ k c hX) ⥤ᵇ
      BasedCategory.ofFunctor (algebraForget_ringInf Λ k c hX) :=
  BasedFunctor.ofFunctor (restrictRingFunctor₁ Λ k c hX)
    (restrictRingFunctor₁_comp_forget Λ k c hX)

/-- The underlying ordinary functor of `restrictRing₁` is `restrictRingFunctor₁`. -/
theorem restrictRing₁_toFunctor :
    (restrictRing₁ Λ k c hX).toFunctor = restrictRingFunctor₁ Λ k c hX :=
  sorry

/-- `restrictRing₁` commutes strictly with the projections to `ArtinianLocalAlgCat`. -/
theorem restrictRing₁_comp_forget :
    (restrictRing₁ Λ k c hX).toFunctor.comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₁ Λ k c hX :=
  sorry

/-- The `A`-algebra of global sections of a deformation of `overlapOpenSpec₂`. -/
def overlapSectionsObj₂ (Y : deformationCategory_overlap₂ Λ k c hX) : FlatAlgebraCat Λ k where
  base := Y.left.base
  algebra := (Γ(Y.left.scheme, ⊤) : Type u)
  isAlgebra := FlatSchemeCat.algebraOfStructureHom Y.left
  isFlat := sorry

/-- The ring map `Γ(W, ⊤) →+* P₁₂` of a deformation of the second overlap open. -/
def overlapSectionsRingHom₂ (Y : deformationCategory_overlap₂ Λ k c hX) :
    Γ(Y.left.scheme, ⊤) →+* Γ(X, c.U₁ ⊓ c.U₂) :=
  (Y.hom.schemeHom.appTop ≫ (overlapIso₂ c).inv.appTop ≫ (c.U₁ ⊓ c.U₂).topIso.hom).hom

/-- The morphism `(A, Γ(W, ⊤)) ⟶ (k, P₁₂)` induced by a deformation of `overlapOpenSpec₂`. -/
def overlapSectionsResidueHom₂ (Y : deformationCategory_overlap₂ Λ k c hX) :
    overlapSectionsObj₂ Λ k c hX Y ⟶ ofResidue_ringInf Λ k c hX :=
  FlatAlgebraCat.Hom.of Y.hom.baseHom (overlapSectionsRingHom₂ Λ k c hX Y) sorry sorry

/-- A morphism of deformations of `overlapOpenSpec₂` induces the map on global sections. -/
def overlapSectionsMap₂ {src tgt : deformationCategory_overlap₂ Λ k c hX} (f : src ⟶ tgt) :
    overlapSectionsObj₂ Λ k c hX src ⟶ overlapSectionsObj₂ Λ k c hX tgt :=
  FlatAlgebraCat.Hom.of f.left.baseHom f.left.schemeHom.appTop.hom sorry sorry

/-- The functor `Def_{overlapOpenSpec₂} ⥤ Def_{P₁₂}` sending `(A, W)` to `(A, Γ(W, ⊤))`. -/
def overlapSectionsFunctor₂ :
    deformationCategory_overlap₂ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX where
  obj Y := Over.mk (overlapSectionsResidueHom₂ Λ k c hX Y)
  map f := Over.homMk (overlapSectionsMap₂ Λ k c hX f) sorry
  map_id := sorry
  map_comp := sorry

/-- The ordinary functor `Def_{P₂} ⥤ Def_{P₁₂}` of restriction along `U₁₂ ⊂ U₂`. -/
def restrictRingFunctor₂ :
    deformationCategory_ring₂ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX :=
  (specFunctor₂ Λ k c hX).comp
    ((FlatSchemeCat.restrictFunctor Λ k (Spec (CommRingCat.of (ring₂ c)))
        (specStructureHom₂ Λ k c hX) (overlapOpenSpec₂ c)).comp
      (overlapSectionsFunctor₂ Λ k c hX))

/-- `restrictRingFunctor₂` lies strictly over `ArtinianLocalAlgCat`. -/
theorem restrictRingFunctor₂_comp_forget :
    (restrictRingFunctor₂ Λ k c hX).comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₂ Λ k c hX :=
  sorry

/-- The morphism `Def_{P₂} ⥤ᵇ Def_{P₁₂}` of categories over `ArtinianLocalAlgCat`. -/
def restrictRing₂ :
    BasedCategory.ofFunctor (algebraForget_ring₂ Λ k c hX) ⥤ᵇ
      BasedCategory.ofFunctor (algebraForget_ringInf Λ k c hX) :=
  BasedFunctor.ofFunctor (restrictRingFunctor₂ Λ k c hX)
    (restrictRingFunctor₂_comp_forget Λ k c hX)

/-- The underlying ordinary functor of `restrictRing₂` is `restrictRingFunctor₂`. -/
theorem restrictRing₂_toFunctor :
    (restrictRing₂ Λ k c hX).toFunctor = restrictRingFunctor₂ Λ k c hX :=
  sorry

/-- `restrictRing₂` commutes strictly with the projections to `ArtinianLocalAlgCat`. -/
theorem restrictRing₂_comp_forget :
    (restrictRing₂ Λ k c hX).toFunctor.comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₂ Λ k c hX :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
