/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Henselian.StrictHenselization.Comparison
public import ReasLib.RingTheory.Henselian.StrictHenselization.Specified
public import stacks_project.Chap93.Example_93_8_1_Rings

/-!
# Strict henselization functor on deformation categories of rings

The functor `Def_P ⥤ Def_{Psh}` sending a deformation `(A, Q) ⟶ (k, P)` to
`(A, Qsh) ⟶ (k, Psh)`, together with the based-functor companion over
`ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory Functor IsLocalRing
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]
variable [IsLocalRing P]

/-- A deformation algebra over a local ring is local. -/
instance instIsLocalRing_deformationAlgebra (ξ : deformationCategory Λ k P) :
    IsLocalRing ξ.left.algebra := sorry

/-- The structure map of a deformation `(A, Q) ⟶ (k, P)` is a local homomorphism. -/
instance instIsLocalHom_deformationHom (ξ : deformationCategory Λ k P) :
    IsLocalHom ξ.hom.toRingHom := sorry

/-- The deformation algebra is a `P`-algebra via the structure map `Q →+* P`. -/
instance instAlgebra_deformationAlgebra (ξ : deformationCategory Λ k P) :
    Algebra ξ.left.algebra P :=
  ξ.hom.toRingHom.toAlgebra

/-- The algebra map `Q → P` of a deformation is local. -/
instance instIsLocalHom_algebraMap_deformationAlgebra (ξ : deformationCategory Λ k P) :
    IsLocalHom (algebraMap ξ.left.algebra P) :=
  instIsLocalHom_deformationHom Λ k P ξ

/-- The `Q`-algebra structure on `Q'` along a morphism of deformations. -/
abbrev algebraAlongMap {ξ η : deformationCategory Λ k P} (f : ξ ⟶ η) :
    Algebra ξ.left.algebra η.left.algebra :=
  f.left.toRingHom.toAlgebra

/-- The algebra map of `algebraAlongMap` is the underlying ring map of `f`. -/
theorem algebraAlongMap_algebraMap {ξ η : deformationCategory Λ k P} (f : ξ ⟶ η) :
    (algebraAlongMap Λ k P f).algebraMap = f.left.toRingHom := sorry

/-- Locality of `Q → Q'` along a morphism of deformations. -/
theorem isLocalHom_algebraAlongMap {ξ η : deformationCategory Λ k P} (f : ξ ⟶ η) :
    IsLocalHom (algebraAlongMap Λ k P f).algebraMap := sorry

variable (Psh : Type u) [CommRing Psh] [Algebra k Psh] [Algebra P Psh]
  [IsScalarTower k P Psh] [IsStrictHenselizationOf P Psh]

/-- The structural map of the given strict henselization is local. -/
instance instIsLocalHom_algebraMap_strictHenselization :
    IsLocalHom (algebraMap P Psh) :=
  IsStrictHenselizationOf.toIsLocalHom

/-- The residue fibre object `(k, P)` has algebra `P`, hence is local. -/
instance instIsLocalRing_residueObj_algebra :
    IsLocalRing (Fiber.fiberInclusion.obj (residueObj Λ k P)).algebra :=
  inferInstanceAs (IsLocalRing P)

/-- Residue-field algebra structure `ResidueField Q → ResidueField Psh` along a
deformation of `P` and the given strict henselization `Psh`. -/
instance instAlgebra_residueField_deformationAlgebra (ξ : deformationCategory Λ k P) :
    Algebra (ResidueField ξ.left.algebra) (ResidueField Psh) :=
  ((ResidueField.map (algebraMap P Psh)).comp
    (@ResidueField.map ξ.left.algebra
      (Fiber.fiberInclusion.obj (residueObj Λ k P)).algebra _ _ _ _
      ξ.hom.toRingHom (instIsLocalHom_deformationHom Λ k P ξ))).toAlgebra

/-- The residue field of `Psh` is a separable closure of the residue field of a
deformation algebra of `P`. -/
instance instIsSepClosure_residueField_deformationAlgebra
    (ξ : deformationCategory Λ k P) :
    IsSepClosure (ResidueField ξ.left.algebra) (ResidueField Psh) := sorry

/-- The deformation algebra acts on the given strict henselization of `P`. -/
instance instAlgebra_deformationAlgebra_target (ξ : deformationCategory Λ k P) :
    Algebra ξ.left.algebra Psh :=
  Algebra.compHom Psh (algebraMap ξ.left.algebra P)

/-- The scalar tower `Q → P → Psh` of a deformation of `P`. -/
instance instIsScalarTower_deformationAlgebra (ξ : deformationCategory Λ k P) :
    IsScalarTower ξ.left.algebra P Psh :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The Type-u strict henselization of the deformation algebra of `ξ`, chosen so
that its residue field is identified with `ResidueField Psh`. -/
noncomputable def strictHenselizationAlgebra (ξ : deformationCategory Λ k P) : Type u :=
  (IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv (ξ.left.algebra) (ResidueField Psh)).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The chosen carrier is a commutative ring. -/
instance instCommRing_strictHenselizationAlgebra (ξ : deformationCategory Λ k P) :
    CommRing (strictHenselizationAlgebra Λ k P Psh ξ) :=
  (IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv (ξ.left.algebra) (ResidueField Psh)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The chosen carrier is an algebra over the deformation algebra `Q`. -/
instance instAlgebra_overSource (ξ : deformationCategory Λ k P) :
    Algebra ξ.left.algebra (strictHenselizationAlgebra Λ k P Psh ξ) :=
  (IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv (ξ.left.algebra) (ResidueField Psh)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The chosen carrier is a strict henselization of the deformation algebra. -/
instance instIsStrictHenselizationOf_strictHenselizationAlgebra
    (ξ : deformationCategory Λ k P) :
    IsStrictHenselizationOf ξ.left.algebra (strictHenselizationAlgebra Λ k P Psh ξ) :=
  (IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv (ξ.left.algebra) (ResidueField Psh)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The chosen carrier is an algebra over the Artinian base of `ξ`. -/
instance instAlgebra_overBase (ξ : deformationCategory Λ k P) :
    Algebra ξ.left.base.carrier (strictHenselizationAlgebra Λ k P Psh ξ) :=
  Algebra.compHom (strictHenselizationAlgebra Λ k P Psh ξ)
    (algebraMap ξ.left.base.carrier ξ.left.algebra)

/-- The chosen strict henselization is flat over the Artinian base of `ξ`. -/
instance instModuleFlat_overBase (ξ : deformationCategory Λ k P) :
    Module.Flat ξ.left.base.carrier (strictHenselizationAlgebra Λ k P Psh ξ) := sorry

/-- The chosen carrier is a strict henselization of the deformation algebra. -/
theorem strictHenselizationAlgebra_spec (ξ : deformationCategory Λ k P) :
    IsStrictHenselizationOf ξ.left.algebra
      (strictHenselizationAlgebra Λ k P Psh ξ) := sorry

/-- Residue-field identification of the chosen strict henselization with
`ResidueField Psh`. -/
noncomputable def strictHenselizationResidueFieldEquiv
    (ξ : deformationCategory Λ k P) :
    ResidueField (strictHenselizationAlgebra Λ k P Psh ξ) ≃+* ResidueField Psh :=
  (IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv (ξ.left.algebra) (ResidueField Psh)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The residue-field identification is compatible with the structural map
`Q → Qsh`. -/
theorem strictHenselizationResidueFieldEquiv_comp
    (ξ : deformationCategory Λ k P) :
    (strictHenselizationResidueFieldEquiv Λ k P Psh ξ).toRingHom.comp
        (ResidueField.map
          (algebraMap ξ.left.algebra (strictHenselizationAlgebra Λ k P Psh ξ))) =
      algebraMap (ResidueField ξ.left.algebra) (ResidueField Psh) := sorry

/-- The unique residue-compatible local comparison `Qsh →+* Psh`. -/
noncomputable def strictHenselizationHom (ξ : deformationCategory Λ k P) :
    strictHenselizationAlgebra Λ k P Psh ξ →+* Psh :=
  (Classical.choose
    (IsStrictHenselizationOf.Comparison.existsUnique_ofResidueMap
      (R := ξ.left.algebra) (S := P)
      (A := strictHenselizationAlgebra Λ k P Psh ξ) (B := Psh)
      (hRS := instAlgebra_deformationAlgebra Λ k P ξ)
      (hRSLocal := instIsLocalHom_algebraMap_deformationAlgebra Λ k P ξ)
      (hRA := instAlgebra_overSource Λ k P Psh ξ)
      (hA := instIsStrictHenselizationOf_strictHenselizationAlgebra Λ k P Psh ξ)
      (hRB := instAlgebra_deformationAlgebra_target Λ k P Psh ξ)
      (hTower := instIsScalarTower_deformationAlgebra Λ k P Psh ξ)
      (strictHenselizationResidueFieldEquiv Λ k P Psh ξ).toRingHom
      sorry)).hom.toRingHom

/-- The comparison `Qsh → Psh` commutes with the maps from the Artinian base. -/
theorem strictHenselizationHom_comp_algebraMap (ξ : deformationCategory Λ k P) :
    (strictHenselizationHom Λ k P Psh ξ).comp
        (algebraMap ξ.left.base.carrier (strictHenselizationAlgebra Λ k P Psh ξ)) =
      (algebraMap k Psh).comp ξ.hom.baseHom.hom.toRingHom := sorry

/-- The comparison `Qsh → Psh` is the unique residue-compatible local `Q`-algebra
map. -/
theorem strictHenselizationHom_unique (ξ : deformationCategory Λ k P)
    (f : strictHenselizationAlgebra Λ k P Psh ξ →ₐ[ξ.left.algebra] Psh)
    [IsLocalHom f.toRingHom]
    (hf : ResidueField.map f.toRingHom =
      (strictHenselizationResidueFieldEquiv Λ k P Psh ξ).toRingHom) :
    f.toRingHom = strictHenselizationHom Λ k P Psh ξ := sorry

/-- The image of a deformation as an object of `F`. -/
noncomputable def strictHenselizationFlatObj (ξ : deformationCategory Λ k P) :
    FlatAlgebraCat Λ k :=
  of ξ.left.base (strictHenselizationAlgebra Λ k P Psh ξ)

/-- The image object in `F` has the same Artinian base as the source deformation. -/
theorem strictHenselizationFlatObj_base (ξ : deformationCategory Λ k P) :
    (strictHenselizationFlatObj Λ k P Psh ξ).base = ξ.left.base := sorry

/-- The image object in `F` has the chosen strict henselization as its algebra. -/
theorem strictHenselizationFlatObj_algebra (ξ : deformationCategory Λ k P) :
    (strictHenselizationFlatObj Λ k P Psh ξ).algebra =
      strictHenselizationAlgebra Λ k P Psh ξ := sorry

/-- The image of a deformation as a morphism `(A, Qsh) ⟶ (k, Psh)` in `F`. -/
noncomputable def strictHenselizationFlatHom (ξ : deformationCategory Λ k P) :
    Hom (strictHenselizationFlatObj Λ k P Psh ξ) (ofResidue Λ k Psh) :=
  Hom.of ξ.hom.baseHom (strictHenselizationHom Λ k P Psh ξ)
    (strictHenselizationHom_comp_algebraMap Λ k P Psh ξ) sorry

/-- The canonical tensor map of the image morphism `(A, Qsh) ⟶ (k, Psh)` is
bijective. -/
theorem strictHenselizationHom_isIso_tensor (ξ : deformationCategory Λ k P) :
    Function.Bijective
      (canonicalTensorMap
        (strictHenselizationFlatHom Λ k P Psh ξ).baseHom
        (strictHenselizationFlatHom Λ k P Psh ξ).toRingHom
        (strictHenselizationFlatHom Λ k P Psh ξ).commutes) := sorry

/-- The image object `(A, Qsh) ⟶ (k, Psh)` in `Def_{Psh}`. -/
noncomputable def strictHenselizationObj (ξ : deformationCategory Λ k P) :
    deformationCategory Λ k Psh :=
  Over.mk (strictHenselizationFlatHom Λ k P Psh ξ)

/-- The image object has the same Artinian base as the source deformation. -/
theorem strictHenselizationObj_base (ξ : deformationCategory Λ k P) :
    (strictHenselizationObj Λ k P Psh ξ).left.base = ξ.left.base := sorry

/-- The image object has the chosen strict henselization as its algebra. -/
theorem strictHenselizationObj_algebra (ξ : deformationCategory Λ k P) :
    (strictHenselizationObj Λ k P Psh ξ).left.algebra =
      strictHenselizationAlgebra Λ k P Psh ξ := sorry

/-- The image morphism induces a bijective canonical tensor map. -/
theorem strictHenselizationObj_isIso_tensor (ξ : deformationCategory Λ k P) :
    Function.Bijective
      (canonicalTensorMap (strictHenselizationObj Λ k P Psh ξ).hom.baseHom
        (strictHenselizationObj Λ k P Psh ξ).hom.toRingHom
        (strictHenselizationObj Λ k P Psh ξ).hom.commutes) := sorry

/-- The `Q`-algebra structure on `Q'sh` obtained by restriction of scalars along
a morphism of deformations. -/
abbrev algebraAlongMap_target {ξ η : deformationCategory Λ k P} (f : ξ ⟶ η) :
    Algebra ξ.left.algebra (strictHenselizationAlgebra Λ k P Psh η) :=
  Algebra.compHom (strictHenselizationAlgebra Λ k P Psh η)
    (algebraAlongMap Λ k P f).algebraMap

/-- Restriction of scalars along `f` acts by the algebra map of `algebraAlongMap`. -/
theorem algebraAlongMap_target_algebraMap {ξ η : deformationCategory Λ k P}
    (f : ξ ⟶ η) :
    (algebraAlongMap_target Λ k P Psh f).algebraMap =
      (algebraMap η.left.algebra (strictHenselizationAlgebra Λ k P Psh η)).comp
        (algebraAlongMap Λ k P f).algebraMap := sorry

/-- The scalar tower `Q → Q' → Q'sh` along a morphism of deformations. -/
theorem isScalarTower_algebraAlongMap {ξ η : deformationCategory Λ k P} (f : ξ ⟶ η) :
    @IsScalarTower ξ.left.algebra η.left.algebra
      (strictHenselizationAlgebra Λ k P Psh η)
      (algebraAlongMap Λ k P f).toSMul
      (instAlgebra_overSource Λ k P Psh η).toSMul
      (algebraAlongMap_target Λ k P Psh f).toSMul := sorry

/-- The unique residue-compatible comparison of chosen strict henselizations
along a morphism of deformations. -/
noncomputable def strictHenselizationMapHom {ξ η : deformationCategory Λ k P}
    (f : ξ ⟶ η) :
    strictHenselizationAlgebra Λ k P Psh ξ →+*
      strictHenselizationAlgebra Λ k P Psh η :=
  -- Local instance justification (noncanonical choice): the Q-algebra structure
  -- on Q'sh is restriction of scalars along the ring map of f, not a canonical
  -- instance on the pair of carriers.
  letI := algebraAlongMap_target Λ k P Psh f
  (Classical.choose
    (IsStrictHenselizationOf.Comparison.existsUnique_ofResidueMap
      (R := ξ.left.algebra) (S := η.left.algebra)
      (A := strictHenselizationAlgebra Λ k P Psh ξ)
      (B := strictHenselizationAlgebra Λ k P Psh η)
      (hRS := algebraAlongMap Λ k P f)
      (hRSLocal := isLocalHom_algebraAlongMap Λ k P f)
      (hRA := instAlgebra_overSource Λ k P Psh ξ)
      (hA := instIsStrictHenselizationOf_strictHenselizationAlgebra Λ k P Psh ξ)
      (hSB := instAlgebra_overSource Λ k P Psh η)
      (hRB := algebraAlongMap_target Λ k P Psh f)
      (hTower := isScalarTower_algebraAlongMap Λ k P Psh f)
      (hB := instIsStrictHenselizationOf_strictHenselizationAlgebra Λ k P Psh η)
      ((strictHenselizationResidueFieldEquiv Λ k P Psh η).symm.toRingHom.comp
        (strictHenselizationResidueFieldEquiv Λ k P Psh ξ).toRingHom)
      sorry)).hom.toRingHom

/-- The comparison of chosen strict henselizations along `f` commutes with the
maps from the Artinian bases. -/
theorem strictHenselizationMapHom_comp_algebraMap
    {ξ η : deformationCategory Λ k P} (f : ξ ⟶ η) :
    (strictHenselizationMapHom Λ k P Psh f).comp
        (algebraMap ξ.left.base.carrier
          (strictHenselizationAlgebra Λ k P Psh ξ)) =
      (algebraMap η.left.base.carrier
          (strictHenselizationAlgebra Λ k P Psh η)).comp
        f.left.baseHom.hom.toRingHom := sorry

/-- The comparison of chosen strict henselizations along `f` is the unique local
`Q`-algebra map whose residue-field map is the prescribed identification of
`ResidueField Qsh` with `ResidueField Q'sh`. -/
theorem strictHenselizationMapHom_unique {ξ η : deformationCategory Λ k P}
    (f : ξ ⟶ η)
    (g : strictHenselizationAlgebra Λ k P Psh ξ →+*
      strictHenselizationAlgebra Λ k P Psh η)
    (hg_alg :
      g.comp (algebraMap ξ.left.algebra
          (strictHenselizationAlgebra Λ k P Psh ξ)) =
        (algebraAlongMap_target Λ k P Psh f).algebraMap)
    (hg_local : IsLocalHom g)
    (hg : @ResidueField.map
        (strictHenselizationAlgebra Λ k P Psh ξ)
        (strictHenselizationAlgebra Λ k P Psh η) _ _ _ _ g hg_local =
      (strictHenselizationResidueFieldEquiv Λ k P Psh η).symm.toRingHom.comp
        (strictHenselizationResidueFieldEquiv Λ k P Psh ξ).toRingHom) :
    g = strictHenselizationMapHom Λ k P Psh f := sorry

/-- The morphism map of the strict henselization functor on deformation
categories. -/
noncomputable def strictHenselizationMap {ξ η : deformationCategory Λ k P}
    (f : ξ ⟶ η) :
    strictHenselizationObj Λ k P Psh ξ ⟶ strictHenselizationObj Λ k P Psh η :=
  Over.homMk
    (Hom.of f.left.baseHom (strictHenselizationMapHom Λ k P Psh f)
      (strictHenselizationMapHom_comp_algebraMap Λ k P Psh f) sorry)
    sorry

/-- The morphism map preserves the underlying arrow in `ArtinianLocalAlgCat`. -/
theorem strictHenselizationMap_baseHom {ξ η : deformationCategory Λ k P}
    (f : ξ ⟶ η) :
    (strictHenselizationMap Λ k P Psh f).left.baseHom = f.left.baseHom := sorry

/-- The functor `Def_P ⥤ Def_{Psh}` sending `(A, Q) ⟶ (k, P)` to
`(A, Qsh) ⟶ (k, Psh)`. -/
noncomputable def strictHenselizationFunctor :
    deformationCategory Λ k P ⥤ deformationCategory Λ k Psh where
  obj := strictHenselizationObj Λ k P Psh
  map := strictHenselizationMap Λ k P Psh
  map_id := sorry
  map_comp := sorry

/-- The ordinary functor sends a deformation to the image object in `Def_{Psh}`. -/
theorem strictHenselizationFunctor_obj (ξ : deformationCategory Λ k P) :
    (strictHenselizationFunctor Λ k P Psh).obj ξ =
      strictHenselizationObj Λ k P Psh ξ := sorry

/-- The functor preserves the Artinian local base of a deformation. -/
theorem strictHenselizationFunctor_obj_base (ξ : deformationCategory Λ k P) :
    ((strictHenselizationFunctor Λ k P Psh).obj ξ).left.base = ξ.left.base := sorry

/-- The functor replaces the algebra of a deformation by its chosen strict
henselization. -/
theorem strictHenselizationFunctor_obj_algebra (ξ : deformationCategory Λ k P) :
    ((strictHenselizationFunctor Λ k P Psh).obj ξ).left.algebra =
      strictHenselizationAlgebra Λ k P Psh ξ := sorry

/-- `strictHenselizationFunctor` lies over `C_Λ`: it commutes with the
projections to `ArtinianLocalAlgCat`. -/
theorem strictHenselizationFunctor_comp_forget :
    strictHenselizationFunctor Λ k P Psh ⋙
        Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k Psh)) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
        (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) := sorry

/-- The functor of deformation categories as a morphism of categories over `C_Λ`. -/
noncomputable def strictHenselizationBasedFunctor :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k Psh)) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) where
  toFunctor := strictHenselizationFunctor Λ k P Psh
  w := strictHenselizationFunctor_comp_forget Λ k P Psh

/-- The underlying functor of `strictHenselizationBasedFunctor` is
`strictHenselizationFunctor`. -/
theorem strictHenselizationBasedFunctor_toFunctor :
    (strictHenselizationBasedFunctor Λ k P Psh).toFunctor =
      strictHenselizationFunctor Λ k P Psh := sorry

end FlatAlgebraCat

end
