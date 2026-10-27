/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.MorphismDatum
public import ReasLib.AlgebraicGeometry.Scheme.Module.ProjFromSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Basis.SectionFamilies

/-!
# Morphisms defined by linear systems

A generating linear map from a vector space into the global sections of an invertible module
defines an explicit quotient, lift, and morphism to the projective scheme of the vector space.
The construction is compatible with subspaces and with homogeneous coordinates after choosing
a basis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The sheaf morphism adjoint to a bundled linear map into global sections. -/
noncomputable def evaluation
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    (Scheme.Modules.pullback X.hom).obj (moduleSheaf k V) ⟶ L :=
  Scheme.Modules.pullbackTildeHom X.hom (ModuleCat.of k V) L ψ

/-- A linear system generates an invertible module when its adjoint evaluation morphism is
epimorphic. -/
def Generates
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Prop :=
  Epi (evaluation X L ψ)

/-- Generation by a linear system is precisely epimorphicity of its adjoint evaluation map. -/
theorem generates_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    Generates X L ψ ↔ Epi (evaluation X L ψ) :=
  Iff.rfl

/-- A generating linear system gives an explicit invertible quotient of the pullback of the
affine module sheaf. -/
noncomputable def quotient
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    CategoryTheory.InvertibleQuotient
      ((Scheme.Modules.pullback X.hom).obj (moduleSheaf k V)) where
  object := L
  isInvertible := inferInstance
  hom := evaluation X L ψ
  hom_epi := hψ

namespace SuppliedModel

/-- The lift classified by the explicit invertible quotient of a generating linear system. -/
noncomputable def lift
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom :=
  hP.liftOfQuotientClass X.hom
    (CategoryTheory.InvertibleQuotient.IsoClass.mk (quotient X L ψ hψ))

/-- The morphism defined by a generating linear system is the morphism underlying its classified
lift. -/
noncomputable def morphism
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    X.left ⟶ scheme k V :=
  (lift hP X L ψ hψ).hom

/-- A morphism has the linear-system specification when it underlies a lift classified by the
explicit quotient built from the given sections. -/
def MorphismSpec
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (φ : X.left ⟶ scheme k V) : Prop :=
  ∃ σ : Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom,
    σ.hom = φ ∧ hP.liftToQuotientClass X.hom σ =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (quotient X L ψ hψ)

/-- The linear-system morphism specification is the equality under the chosen quotient
representation, together with the underlying morphism equality. -/
theorem morphismSpec_iff
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (φ : X.left ⟶ scheme k V) :
    MorphismSpec hP X L ψ hψ φ ↔
      ∃ σ : Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom,
        σ.hom = φ ∧ hP.liftToQuotientClass X.hom σ =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (quotient X L ψ hψ) :=
  Iff.rfl

/-- The explicitly constructed morphism is classified by the quotient of its generating linear
system. -/
theorem morphism_spec
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    MorphismSpec hP X L ψ hψ (morphism hP X L ψ hψ) := sorry

/-- The chosen projective-bundle representation classifies a unique morphism with the given
linear-system quotient. -/
theorem existsUnique_morphism
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    ∃! φ : X.left ⟶ scheme k V,
      MorphismSpec hP X L ψ hψ φ := sorry

/-- Pulling the tautological module back along the linear-system morphism yields the given
invertible module. -/
noncomputable def pullbackTautologicalSheafIso
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    (Scheme.Modules.pullback (morphism hP X L ψ hψ)).obj
        (tautologicalSheaf hP) ≅ L :=
  (hP.pullbackTautologicalSheafIso X.hom (lift hP X L ψ hψ)).trans
    (CategoryTheory.InvertibleQuotient.targetIsoOfMkEq
      (hP.liftOfQuotientClass_eq X.hom
        (CategoryTheory.InvertibleQuotient.IsoClass.mk (quotient X L ψ hψ))))

/-- The map on global sections induced from the tautological quotient and its pullback
identification is the original bundled linear map. -/
theorem inducedLinearMap_eq
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    Scheme.Modules.pullbackTildeHomEquiv X.hom (ModuleCat.of k V) L
      ((Scheme.ProjectiveBundle.Lift.pullbackSourceIso
          (lift hP X L ψ hψ) (moduleSheaf k V)).inv ≫
        (Scheme.Modules.pullback (morphism hP X L ψ hψ)).map
          (Scheme.ProjectiveBundle.tautologicalQuotient
            (toSpec k V) hP).hom ≫
        (pullbackTautologicalSheafIso hP X L ψ hψ).hom) = ψ := sorry

end SuppliedModel

/-- An actual local trivialization of the invertible module. We use all such charts rather
than choosing one from an admitted existence theorem. -/
structure TrivializingChart
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules) where
  /-- The source open. -/
  U : X.left.Opens
  /-- The open is affine, so its section ring sees the generating epimorphism. -/
  isAffine : IsAffineOpen U
  /-- A specified trivialization on that affine open. -/
  trivialization : (Scheme.Modules.pullback U.ι).obj L ≅
    SheafOfModules.unit U.toScheme.ringCatSheaf

/-- Coefficients of the restricted sections in a specified local trivialization. -/
noncomputable def chartCoefficient
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (c : TrivializingChart X L) (v : V) : Γ(c.U.toScheme, ⊤) :=
  ((c.trivialization.hom.val.app (Opposite.op ⊤)).hom)
    ((Scheme.Modules.globalSectionsPullback c.U.ι L).hom (ψ v))

/-- The actual symmetric-algebra map on a trivializing chart sends each vector to the
coefficient of its section. -/
noncomputable def chartRingHom
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (c : TrivializingChart X L) : SymmetricAlgebra k V →+* Γ(c.U.toScheme, ⊤) :=
  letI : Algebra k Γ(c.U.toScheme, ⊤) :=
    Scheme.Hom.globalSectionsAlgebra (c.U.ι ≫ X.hom)
  (SymmetricAlgebra.lift
    ({ toFun := chartCoefficient X L ψ c
       map_add' := by intros; sorry
       map_smul' := by intros; sorry } : V →ₗ[k] Γ(c.U.toScheme, ⊤))).toRingHom

/-- The coefficient ring homomorphism has the prescribed value on each degree-one vector. -/
theorem chartRingHom_ι
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (c : TrivializingChart X L) (v : V) :
    chartRingHom X L ψ c (SymmetricAlgebra.ι k V v) =
      chartCoefficient X L ψ c v := by
  simp [chartRingHom]

/-- Generation makes the image of the irrelevant ideal the unit ideal in every local
trivialization. This is a property of the explicit coefficient map. -/
theorem chartRingHom_irrelevant
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (c : TrivializingChart X L) :
    (HomogeneousIdeal.irrelevant (grading k V)).toIdeal.map
      (chartRingHom X L ψ c) = ⊤ := sorry

/-- The actual local section-to-Proj morphism in the specified trivialization. -/
noncomputable def chartMorphism
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (c : TrivializingChart X L) :
    c.U.toScheme ⟶ scheme k V :=
  Proj.fromOfGlobalSections (grading k V) (chartRingHom X L ψ c)
    (chartRingHom_irrelevant X L ψ hψ c)

/-- All specified trivializations cover an invertible module's source. -/
theorem trivializingCharts_cover
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L] :
    (⨆ c : TrivializingChart X L, c.U) = ⊤ := sorry

/-- The cover used by the canonical construction consists of all actual local trivializations. -/
noncomputable def trivializingCover
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L] : X.left.OpenCover :=
  X.left.openCoverOfIsOpenCover (fun c : TrivializingChart X L ↦ c.U)
    (trivializingCharts_cover X L)

/-- The coefficient constructions agree on overlaps: changing a trivialization multiplies all
homogeneous coordinates by the same unit. -/
theorem chartMorphism_overlap
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (c d : TrivializingChart X L) :
    CategoryTheory.Limits.pullback.fst
          ((trivializingCover X L).f c) ((trivializingCover X L).f d) ≫
        chartMorphism X L ψ hψ c =
      CategoryTheory.Limits.pullback.snd
          ((trivializingCover X L).f c) ((trivializingCover X L).f d) ≫
        chartMorphism X L ψ hψ d := sorry

/-- The canonical section-to-Proj morphism is obtained by gluing the actual coefficient maps.
Its data do not depend on any projective-bundle representation or admitted inverse. -/
noncomputable def morphism
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) : X.left ⟶ scheme k V :=
  (trivializingCover X L).glueMorphisms (chartMorphism X L ψ hψ)
    (chartMorphism_overlap X L ψ hψ)

/-- The canonical morphism has precisely the coefficient map on every trivializing chart. -/
theorem morphism_chart
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (c : TrivializingChart X L) :
    c.U.ι ≫ morphism X L ψ hψ = chartMorphism X L ψ hψ c :=
  (trivializingCover X L).ι_glueMorphisms _ _ c

/-- The canonical map is over the original affine base. -/
theorem morphism_toSpec
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    morphism X L ψ hψ ≫ toSpec k V = X.hom := sorry

/-- The actual canonical morphism bundled with its base triangle. -/
noncomputable def lift
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) : Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom :=
  ⟨morphism X L ψ hψ, morphism_toSpec X L ψ hψ⟩

/-- A morphism has the canonical linear-system specification when its local coefficient
morphisms agree on every actual trivializing chart. -/
def MorphismSpec
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (φ : X.left ⟶ scheme k V) : Prop :=
  ∀ c : TrivializingChart X L, c.U.ι ≫ φ = chartMorphism X L ψ hψ c

/-- The linear-system specification is its actual local coordinate description. -/
theorem morphismSpec_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (φ : X.left ⟶ scheme k V) :
    MorphismSpec X L ψ hψ φ ↔
      ∀ c : TrivializingChart X L, c.U.ι ≫ φ = chartMorphism X L ψ hψ c := Iff.rfl

/-- The glued canonical morphism has the prescribed local coordinates. -/
theorem morphism_spec
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    MorphismSpec X L ψ hψ (morphism X L ψ hψ) := morphism_chart X L ψ hψ

/-- The local coordinate specification determines a unique morphism. -/
theorem existsUnique_morphism
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    ∃! φ : X.left ⟶ scheme k V, MorphismSpec X L ψ hψ φ := sorry

/-- All opens form a basis; this is used only to extend specified section maps. -/
theorem allOpens_isBasis (Y : Scheme.{u}) :
    TopologicalSpace.Opens.IsBasis (Set.univ : Set Y.Opens) := by sorry

/-- On U mapping into a degree-one standard open, send an actual section s of O(1) to
phi*(s/v) times the given section psi(v). This is the explicit local tautological comparison. -/
noncomputable def tautologicalPushforwardFamily
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    TopCat.Presheaf.BasisPushforwardHomFamily (morphism X L ψ hψ).base
      (Set.univ : Set X.left.Opens) (tautologicalBasis (k := k) (V := V))
      (canonicalTautologicalSheaf (k := k) (V := V)).val.presheaf L.val.presheaf where
  app U W h :=
    let v := Classical.choose W.property
    let hv := Classical.choose_spec W.property
    AddCommGrpCat.ofHom
      (X := (canonicalTautologicalSheaf (k := k) (V := V)).val.presheaf.obj (Opposite.op W.obj))
      (Y := L.val.presheaf.obj (Opposite.op U.obj))
      { toFun := fun s ↦
          SMul.smul (α := L.val.obj (Opposite.op U.obj))
            (((morphism X L ψ hψ).appLE W.obj U.obj h).hom
              (tautologicalRatio v W.obj hv s))
            ((L.val.map (homOfLE (show U.obj ≤ ⊤ from le_top)).op).hom (ψ v))
        map_zero' := by sorry
        map_add' := by intros; sorry }
  source_naturality := by intros; sorry
  target_naturality := by intros; sorry

/-- The ratio-and-section formula is linear over the actual structure-sheaf map of phi. -/
noncomputable def tautologicalPushforwardLinearFamily
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    RingedSpace.Module.BasisPushforwardHomFamily.LinearFamily
      (BX := (Set.univ : Set X.left.Opens))
      (BY := tautologicalBasis (k := k) (V := V))
      (ℱ := L) (𝒢 := canonicalTautologicalSheaf (k := k) (V := V))
      (morphism X L ψ hψ).toShHom :=
  ⟨tautologicalPushforwardFamily X L ψ hψ, by intros; sorry⟩

/-- Extend the specified homogeneous-ratio formulas to the actual sheaf morphism O(1)→phi_*L. -/
noncomputable def tautologicalPushforwardHom
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    canonicalTautologicalSheaf (k := k) (V := V) ⟶
      (Scheme.Modules.pushforward (morphism X L ψ hψ)).obj L :=
  RingedSpace.Module.BasisPushforwardHomFamily.toHom
    (morphism X L ψ hψ).toShHom (allOpens_isBasis X.left)
    tautologicalBasis_isBasis (tautologicalPushforwardLinearFamily X L ψ hψ)

/-- The forward tautological comparison is the actual pullback-pushforward adjoint of the
homogeneous-ratio sheaf morphism. -/
noncomputable def pullbackTautologicalHom
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    (Scheme.Modules.pullback (morphism X L ψ hψ)).obj
      (canonicalTautologicalSheaf (k := k) (V := V)) ⟶ L :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (morphism X L ψ hψ)).homEquiv _ _).symm
    (tautologicalPushforwardHom X L ψ hψ)

/-- Explicit section coordinates on an open where one of the given sections is a generator.
These are input coordinates for a local formula, not a chosen inverse of a sheaf morphism. -/
structure SectionFrame
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (U : X.left.Opens) where
  /-- Coordinates of all module sections in a specified frame. -/
  coefficient : L.val.obj (Opposite.op U) ≃ₗ[X.left.presheaf.obj (Opposite.op U)]
    X.left.presheaf.obj (Opposite.op U)
  /-- A vector whose section is invertible in this frame. -/
  vector : V
  /-- An actual unit giving the coefficient, including its inverse as data. -/
  coefficientUnit : (X.left.presheaf.obj (Opposite.op U))ˣ
  /-- The supplied unit is exactly the chosen section's coefficient. -/
  coefficientUnit_eq : (coefficientUnit : X.left.presheaf.obj (Opposite.op U)) =
    coefficient ((L.val.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (ψ vector))

/-- Source opens carrying explicit section-frame coordinates. -/
def sectionFrameBasis
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Set X.left.Opens :=
  {U | Nonempty (SectionFrame X L ψ U)}

/-- The nonvanishing opens of a generating family give section frames locally. -/
theorem sectionFrameBasis_isBasis
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    TopologicalSpace.Opens.IsBasis (sectionFrameBasis X L ψ) := sorry

/-- The inverse comparison on a section frame is the explicit formula
s ↦ coefficient(s)/coefficient(psi(v)) times phi*(v/1). The frame is read from the basis-open
membership data; no inverse is extracted from the comparison's isomorphism property. -/
noncomputable def tautologicalInverseFamily
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    TopCat.Presheaf.BasisPushforwardHomFamily (𝟙 X.left : X.left ⟶ X.left).base
      (sectionFrameBasis X L ψ) (Set.univ : Set X.left.Opens) L.val.presheaf
      ((Scheme.Modules.pullback (morphism X L ψ hψ)).obj
        (canonicalTautologicalSheaf (k := k) (V := V))).val.presheaf where
  app U W h :=
    let c := Classical.choice U.property
    let F := (Scheme.Modules.pullback (morphism X L ψ hψ)).obj
      (canonicalTautologicalSheaf (k := k) (V := V))
    let pulledSection := (Scheme.Modules.globalSectionsPullback (morphism X L ψ hψ)
      (canonicalTautologicalSheaf (k := k) (V := V))).hom
        (tautologicalSection c.vector)
    AddCommGrpCat.ofHom
      (X := L.val.presheaf.obj (Opposite.op W.obj))
      (Y := F.val.presheaf.obj (Opposite.op U.obj))
      { toFun := fun s ↦
          SMul.smul (α := F.val.obj (Opposite.op U.obj))
            (c.coefficient ((L.val.map (homOfLE h).op).hom s) *
              (↑(c.coefficientUnit⁻¹) : X.left.presheaf.obj (Opposite.op U.obj)))
            ((F.val.map (homOfLE (show U.obj ≤ ⊤ from le_top)).op).hom pulledSection)
        map_zero' := by sorry
        map_add' := by intros; sorry }
  source_naturality := by intros; sorry
  target_naturality := by intros; sorry

/-- The explicit inverse formulas are module-linear in the source sections. -/
noncomputable def tautologicalInverseLinearFamily
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    RingedSpace.Module.BasisPushforwardHomFamily.LinearFamily
      (BX := sectionFrameBasis X L ψ) (BY := (Set.univ : Set X.left.Opens))
      (ℱ := (Scheme.Modules.pullback (morphism X L ψ hψ)).obj
        (canonicalTautologicalSheaf (k := k) (V := V))) (𝒢 := L) (𝟙 X.left : X.left ⟶ X.left).toShHom :=
  ⟨tautologicalInverseFamily X L ψ hψ, by intros; sorry⟩

/-- Extend the explicit reciprocal-coefficient formulas to the inverse sheaf morphism. -/
noncomputable def pullbackTautologicalInv
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    L ⟶ (Scheme.Modules.pullback (morphism X L ψ hψ)).obj
      (canonicalTautologicalSheaf (k := k) (V := V)) :=
  RingedSpace.Module.BasisPushforwardHomFamily.toHom (𝟙 X.left : X.left ⟶ X.left).toShHom
    (sectionFrameBasis_isBasis X L ψ hψ) (allOpens_isBasis X.left)
    (tautologicalInverseLinearFamily X L ψ hψ) ≫
    (Scheme.Modules.pushforwardId X.left).hom.app _

/-- The tautological isomorphism of the canonical section-to-Proj map, with both morphisms
constructed from their local formulas. Only the two inverse laws are proposition-valued fields. -/
noncomputable def pullbackTautologicalSheafIso
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    (Scheme.Modules.pullback (morphism X L ψ hψ)).obj
      (canonicalTautologicalSheaf (k := k) (V := V)) ≅ L where
  hom := pullbackTautologicalHom X L ψ hψ
  inv := pullbackTautologicalInv X L ψ hψ
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- The canonical comparison sends the actual homogeneous section v/1 to the original section
psi(v), fixing its normalization in the symmetric-algebra coordinates. -/
theorem inducedLinearMap_eq
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (v : V) :
    (Scheme.Modules.globalSectionsMap (pullbackTautologicalSheafIso X L ψ hψ).hom).hom
      ((Scheme.Modules.globalSectionsPullback (morphism X L ψ hψ)
        (canonicalTautologicalSheaf (k := k) (V := V))).hom (tautologicalSection v)) = ψ v := sorry

/-- The actual tautological quotient pulled back by the canonical map is the original
section-evaluation quotient after its explicit target comparison. -/
theorem pullbackTautologicalSheafIso_quotient
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    (Scheme.ProjectiveBundle.Lift.pullbackSourceIso (lift X L ψ hψ) (moduleSheaf k V)).inv ≫
        (Scheme.Modules.pullback (morphism X L ψ hψ)).map canonicalTautologicalMap ≫
        (pullbackTautologicalSheafIso X L ψ hψ).hom = evaluation X L ψ := sorry

/-- A supplied model agrees with the canonical section-to-Proj construction once its actual
quotient is explicitly normalized to the fixed symmetric-algebra tautological coordinates. -/
theorem SuppliedModel.morphism_eq_canonical
    (hP : Scheme.ProjectiveBundle.Representation (toSpec k V) (moduleSheaf k V))
    (coordinates : CanonicalCoordinates hP)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    SuppliedModel.morphism hP X L ψ hψ =
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.morphism X L ψ hψ := sorry

/-- A generating subspace defines the canonical morphism for its inclusion. -/
noncomputable def subspaceMorphism
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    (hW : Generates X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)) :
    X.left ⟶ scheme k W :=
  morphism X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) hW

/-- The subspace morphism has the coordinates of the inclusion sections. -/
theorem subspaceMorphism_spec
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    (hW : Generates X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)) :
    MorphismSpec X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) hW
      (subspaceMorphism X L W hW) := morphism_spec X L _ hW

/-- The family of sections obtained by evaluating a linear map on a chosen basis. -/
def basisSections
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    Fin (n + 1) → Scheme.Hom.globalSectionsMod X.hom L :=
  fun i ↦ ψ (b i)

/-- A basis section is the image of the corresponding basis vector. -/
theorem basisSections_apply
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (i : Fin (n + 1)) :
    basisSections n b X L ψ i = ψ (b i) :=
  rfl

/-- A morphism to standard projective space has the basis specification when it is associated
to degree-one data whose coordinate sections are the images of the chosen basis vectors. -/
def BasisMorphismSpec
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (φ : X.left ⟶ ProjectiveSpace.scheme k n) : Prop :=
  ∃ τ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading k n) X.left,
    Proj.DegreeOneMorphismDatum.AssociatedTo
        (ProjectiveSpace.grading k n) τ φ ∧
      ∃ e : RingedSpace.TensorPower.sheaf τ.lineBundle 1 ≅ L,
        ∀ i : Fin (n + 1),
          SheafOfModules.sectionsMap e.hom
            (RingedSpace.sectionFromTop
              (RingedSpace.TensorPower.sheaf τ.lineBundle 1)
              (tensorPowerSectionRingProj τ.lineBundle 1
                (τ.sectionMap
                  (DirectSum.of
                    (fun d : ℕ ↦ ProjectiveSpace.grading k n (d * 1)) 1
                    (Eq.mp
                      (congrArg
                        (fun d : ℕ ↦ ↥(ProjectiveSpace.grading k n d))
                        (Nat.mul_one 1).symm)
                      ⟨ProjectiveSpace.coordinate n i,
                        ProjectiveSpace.coordinate_mem_grading_one n i⟩))))) =
            RingedSpace.sectionFromTop L (basisSections n b X L ψ i)

/-- The basis-morphism specification is the existence of associated degree-one data and a
coordinate-compatible identification of its line bundle. -/
theorem basisMorphismSpec_iff
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (φ : X.left ⟶ ProjectiveSpace.scheme k n) :
    BasisMorphismSpec n b X L ψ φ ↔
      ∃ τ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading k n) X.left,
        Proj.DegreeOneMorphismDatum.AssociatedTo
            (ProjectiveSpace.grading k n) τ φ ∧
          ∃ e : RingedSpace.TensorPower.sheaf τ.lineBundle 1 ≅ L,
            ∀ i : Fin (n + 1),
              SheafOfModules.sectionsMap e.hom
                (RingedSpace.sectionFromTop
                  (RingedSpace.TensorPower.sheaf τ.lineBundle 1)
                  (tensorPowerSectionRingProj τ.lineBundle 1
                    (τ.sectionMap
                      (DirectSum.of
                        (fun d : ℕ ↦ ProjectiveSpace.grading k n (d * 1)) 1
                        (Eq.mp
                          (congrArg
                            (fun d : ℕ ↦ ↥(ProjectiveSpace.grading k n d))
                            (Nat.mul_one 1).symm)
                          ⟨ProjectiveSpace.coordinate n i,
                            ProjectiveSpace.coordinate_mem_grading_one n i⟩))))) =
                RingedSpace.sectionFromTop L (basisSections n b X L ψ i) :=
  Iff.rfl

/-- After choosing a basis, the linear-system morphism followed by the basis comparison is the
corresponding morphism to standard projective space. -/
noncomputable def basisMorphism
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    X.left ⟶ ProjectiveSpace.scheme k n :=
  morphism X L ψ hψ ≫ basisComparison n b

/-- The explicit basis composite has the coordinate description determined by the basis
sections. -/
theorem basisMorphism_spec
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    BasisMorphismSpec n b X L ψ (basisMorphism n b X L ψ hψ) := sorry

/-- The basis-coordinate comparison diagram commutes by construction. -/
theorem morphism_basisComparison
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    morphism X L ψ hψ ≫ basisComparison n b =
      basisMorphism n b X L ψ hψ :=
  rfl

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem
