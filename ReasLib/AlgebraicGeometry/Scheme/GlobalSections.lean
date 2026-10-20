/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec

/-!
# Global functions relative to an affine base

This leaf packages the algebra on global functions induced by a morphism to an
affine scheme, together with the corresponding morphism of spectra. It is
independent of any field hypothesis and of any module-sheaf construction.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The ring of global functions on a scheme is an intrinsic scheme datum.  A
structure morphism, when present, only supplies a map into this ring. -/
@[stacks 01JH "global-sections ring carrier"]
abbrev globalSectionsRing (X : Scheme.{u}) : CommRingCat.{u} :=
  Γ(X, ⊤)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- The ring map underlying the global-sections algebra induced by `f`.  The
map is the primary morphism-dependent datum; algebra structures and affine
maps are derived from it. -/
@[stacks 01JH "global-sections map over an affine base"]
noncomputable abbrev globalSectionsMap
    (f : X ⟶ Spec (CommRingCat.of R)) :
    R →+* Scheme.globalSectionsRing X :=
  (Scheme.homToSpecGlobalSectionsEquiv X (CommRingCat.of R) f).hom

/-- The explicit global-sections map agrees with the usual pullback along `f`.
This bridge lets downstream proofs rewrite without unfolding the representing equivalence. -/
@[stacks 01JH "global-sections map pullback bridge"]
theorem globalSectionsMap_eq_appTop
    (f : X ⟶ Spec (CommRingCat.of R)) :
    globalSectionsMap f =
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv) ≫ f.appTop).hom := sorry

/-- The `R`-algebra on global functions induced by the explicit map `f`.
This is a derived compatibility view of `globalSectionsMap f`. -/
@[stacks 01JH "global-sections algebra induced by a map"]
noncomputable abbrev globalSectionsAlgebra
    (f : X ⟶ Spec (CommRingCat.of R)) :
    Algebra R (Scheme.globalSectionsRing X) :=
  (globalSectionsMap f).toAlgebra

/-- The global-sections ring together with the algebra structure induced by `f`.
Keeping this as a bundled object preserves the structure morphism in the type,
so algebraic consumers do not have to reconstruct a noncanonical instance. -/
@[stacks 01JH "global-sections algebra object"]
noncomputable def globalSectionsAlg
    (f : X ⟶ Spec (CommRingCat.of R)) : CommAlgCat R :=
  @CommAlgCat.of R _ (Scheme.globalSectionsRing X) _ (globalSectionsAlgebra f)

/-- The base-ring map viewed as the map into the bundled global-sections algebra. -/
@[stacks 01JH "global-sections bundled algebra map"]
noncomputable abbrev globalSectionsAlgMap
    (f : X ⟶ Spec (CommRingCat.of R)) :
    R →+* globalSectionsAlg f :=
  globalSectionsMap f

/-- The affine morphism `Spec Γ(X, ⊤) ⟶ Spec R` induced by the global-functions algebra of
`f : X ⟶ Spec R`. -/
@[stacks 01JH "global-sections affine map"]
noncomputable abbrev globalSectionsSpecMap
    (f : X ⟶ Spec (CommRingCat.of R)) :
    Spec (Scheme.globalSectionsRing X) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (globalSectionsMap f))

/-- The ring map on sections induced by a scheme morphism over an inclusion of opens. -/
@[stacks 01BH "section-ring map along a scheme morphism"]
noncomputable abbrev sectionsMapAlong
    {Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V) :
    Γ(Y, V) →+* Γ(X, U) :=
  (f.appLE V U hU).hom

/-- The section-ring map is independent of the proof of the open containment. -/
@[stacks 01BH "section-ring map proof independence"]
theorem sectionsMapAlong_proof_irrel
    {Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hU hU' : U ≤ f ⁻¹ᵁ V) :
    sectionsMapAlong f V U hU = sectionsMapAlong f V U hU' := sorry

/-- Restricting the source open composes with the section-ring map. -/
@[stacks 01BH "section-ring map restriction coherence"]
theorem sectionsMapAlong_restrict
    {Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U U' : X.Opens)
    (hU : U ≤ f ⁻¹ᵁ V) (hU' : U' ≤ U) :
    CommRingCat.ofHom (sectionsMapAlong f V U hU) ≫
        X.presheaf.map (homOfLE hU').op =
      CommRingCat.ofHom (sectionsMapAlong f V U' (hU'.trans hU)) := sorry

/-- Restricting the target open before applying the section-ring map agrees with enlarging the
target open in the containment proof. -/
@[stacks 01BH "section-ring map target restriction coherence"]
theorem restrict_sectionsMapAlong
    {Y : Scheme.{u}} (f : X ⟶ Y) (V V' : Y.Opens) (U : X.Opens)
    (hV : V' ≤ V) (hU : U ≤ f ⁻¹ᵁ V') :
    Y.presheaf.map (homOfLE hV).op ≫
        CommRingCat.ofHom (sectionsMapAlong f V' U hU) =
      CommRingCat.ofHom
        (sectionsMapAlong f V U (hU.trans (f.preimage_mono hV))) := sorry

/-- Section-ring maps compose along a composite scheme morphism. -/
@[stacks 01BH "section-ring map composition coherence"]
theorem sectionsMapAlong_comp
    {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Z.Opens) (V : Y.Opens) (U : X.Opens)
    (hV : V ≤ g ⁻¹ᵁ W) (hU : U ≤ f ⁻¹ᵁ V) :
    CommRingCat.ofHom (sectionsMapAlong g W V hV) ≫
        CommRingCat.ofHom (sectionsMapAlong f V U hU) =
      CommRingCat.ofHom
        (sectionsMapAlong (f ≫ g) W U (hU.trans (f.preimage_mono hV))) := sorry

/-- The algebra on section rings induced by `f : X ⟶ Y` over an inclusion
`U ⊆ f⁻¹(V)` of open subsets. -/
@[stacks 01BH "section-ring algebra along a scheme morphism"]
noncomputable abbrev sectionsAlgebra
    {Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V) :
    Algebra Γ(Y, V) Γ(X, U) :=
  (sectionsMapAlong f V U hU).toAlgebra

/-- The section ring on `U`, bundled as an algebra over the section ring on `V` through `f`. -/
@[stacks 01BH "bundled section-ring algebra along a scheme morphism"]
noncomputable def sectionsAlg
    {Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V) :
    CommAlgCat Γ(Y, V) :=
  @CommAlgCat.of Γ(Y, V) _ Γ(X, U) _ (sectionsAlgebra f V U hU)

/-- The bundled section algebra is independent of the proof of the open containment. -/
@[stacks 01BH "bundled section algebra proof independence"]
theorem sectionsAlg_proof_irrel
    {Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hU hU' : U ≤ f ⁻¹ᵁ V) :
    sectionsAlg f V U hU = sectionsAlg f V U hU' := sorry

/-- The ring map on sections induced by a morphism to `Spec R`.  This is the map-level form of
`sectionsAlgebraOverSpec`, so downstream predicates can avoid rebuilding a local `Algebra`
instance merely to write `algebraMap R Γ(X, U)`. -/
@[stacks 01BH "section-ring map over an affine base"]
noncomputable abbrev sectionsMap
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (((Scheme.ΓSpecIso (CommRingCat.of R)).inv) ≫
    f.appLE ⊤ U le_top).hom

/-- The affine-base section map is the general section map after the canonical identification
`R ≅ Γ(Spec R, ⊤)`. -/
@[stacks 01BH "affine-base section-map bridge"]
theorem sectionsMap_eq_sectionsMapAlong
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    CommRingCat.ofHom (sectionsMap f U) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        CommRingCat.ofHom (sectionsMapAlong f ⊤ U le_top) := sorry

/-- Restriction between source opens commutes with the affine-base section map. -/
@[simp, stacks 01BH "affine-base section-map restriction coherence"]
theorem sectionsMap_restrict
    (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens) (hU : U' ≤ U) :
    CommRingCat.ofHom (sectionsMap f U) ≫
        X.presheaf.map (homOfLE hU).op =
      CommRingCat.ofHom (sectionsMap f U') := sorry

/-- The top-section specialization of `sectionsMap` is the global-sections map. -/
@[simp, stacks 01JH "top-section global-sections map bridge"]
theorem sectionsMap_top (f : X ⟶ Spec (CommRingCat.of R)) :
    sectionsMap f (⊤ : X.Opens) = globalSectionsMap f := sorry

/-- A morphism `f : X ⟶ Spec R` induces the canonical `R`-algebra structure on the section
ring `Γ(X, U)` of every open subset `U` of `X`. -/
@[stacks 01BH "section-ring algebra over an affine base"]
noncomputable abbrev sectionsAlgebraOverSpec
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    Algebra R Γ(X, U) :=
  (sectionsMap f U).toAlgebra

/-- The section ring on `U`, bundled as an `R`-algebra through `f : X ⟶ Spec R`. -/
@[stacks 01BH "bundled section-ring algebra over an affine base"]
noncomputable def sectionsAlgOverSpec
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : CommAlgCat R :=
  @CommAlgCat.of R _ Γ(X, U) _ (sectionsAlgebraOverSpec f U)

end AlgebraicGeometry.Scheme.Hom


