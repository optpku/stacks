/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.14.4 (1): a morphism is locally of type `P` exactly when every map on sections
induced by compatible affine opens has property `P`. -/
@[stacks 01SU] #check
  (AlgebraicGeometry.locallyOfType_iff_forall_affineOpen_appLE :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
      (hP : RingHom.PropertyIsLocal P),
      AlgebraicGeometry.LocallyOfType P f ↔
        ∀ {V : S.Opens}, IsAffineOpen V →
          ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            P (f.appLE V U e).hom)

/- Lemma 29.14.4 (2): a morphism is locally of type `P` exactly when the target has an open
cover whose pullbacks have open covers by morphisms locally of type `P`. -/
@[stacks 01SU] #check
  (AlgebraicGeometry.locallyOfType_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
      (hP : RingHom.PropertyIsLocal P),
      AlgebraicGeometry.LocallyOfType P f ↔
        ∃ 𝒱 : S.OpenCover,
          ∀ j : 𝒱.I₀,
            ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
              ∀ i : 𝒰.I₀,
                AlgebraicGeometry.LocallyOfType P (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Lemma 29.14.4 (3): a morphism is locally of type `P` exactly when the target has an affine
open cover whose pullbacks have affine open covers with all induced maps on global sections
satisfying `P`. -/
@[stacks 01SU] #check
  (AlgebraicGeometry.locallyOfType_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
      (hP : RingHom.PropertyIsLocal P),
      AlgebraicGeometry.LocallyOfType P f ↔
        ∃ 𝒱 : S.AffineOpenCover,
          ∀ j : 𝒱.I₀,
            ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
              ∀ i : 𝒰.I₀,
                P ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom)

/- Lemma 29.14.4 (4): restricting a morphism locally of type `P` to compatible open
subschemes preserves the property of being locally of type `P`. -/
@[stacks 01SU] #check
  (AlgebraicGeometry.locallyOfType_resLE :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
      (hP : RingHom.PropertyIsLocal P)
      (hf : AlgebraicGeometry.LocallyOfType P f)
      {V : S.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V),
      AlgebraicGeometry.LocallyOfType P (f.resLE V U e))
