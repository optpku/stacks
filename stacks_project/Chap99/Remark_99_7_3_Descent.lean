module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap70.Lemma_70_7_2_FinitePresentation
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap74.Proposition_74_4_1_Fpqc
public import stacks_project.Chap99.Remark_99_7_3_Quotient

/-!
# Compatible families of quasi-coherent quotients along an fpqc covering

Given an fpqc covering of an algebraic space and fpqc coverings of the pairwise
fibre products, a compatible family is a family of quasi-coherent quotients of
the pulled-back module that restrict to the same quotient on each overlap.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Whiskering the fibre-product square `X_i ×_X X_j` along a morphism from a test
space. -/
theorem overlap_w {Y Z W : AlgebraicSpace S} {fY : Y ⟶ X} {fZ : Z ⟶ X}
    (p : W ⟶ Limits.pullback fY fZ) :
    (p ≫ Limits.pullback.fst fY fZ) ≫ fY = (p ≫ Limits.pullback.snd fY fZ) ≫ fZ :=
  sorry

/-- Source-transport a pulled-back quotient of `f^* F` to a quotient of `(p ≫ f)^* F`. -/
def restrictAlong {F : X.Modules} [F.IsQuasicoherent] {Y W : AlgebraicSpace S}
    {f : Y ⟶ X} (Q : Quotient ((Modules.pullback f).obj F)) (p : W ⟶ Y) :
    Quotient ((Modules.pullback (p ≫ f)).obj F) :=
  Quotient.precomposeIso ((Modules.pullbackComp p f).symm.app F) (Q.pullback p)

/-- Two quasi-coherent quotients of pullbacks of `F` restrict to the same quotient
on a test space when the pulled-back quotients are kernel-identified after
source transport along `Modules.pullbackComp`. -/
def sameRestriction {F : X.Modules} [F.IsQuasicoherent] {Y Z W : AlgebraicSpace S}
    {fY : Y ⟶ X} {fZ : Z ⟶ X}
    (QY : Quotient ((Modules.pullback fY).obj F))
    (QZ : Quotient ((Modules.pullback fZ).obj F))
    (pY : W ⟶ Y) (pZ : W ⟶ Z) (hp : pY ≫ fY = pZ ≫ fZ) : Prop :=
  Quotient.Rel (restrictAlong QY pY)
    (Quotient.precomposeIso
      ((Modules.pullbackCongr hp).app F ≪≫ (Modules.pullbackComp pZ fZ).symm.app F)
      (QZ.pullback pZ))

/-- Agreement of restricted quotients on an fpqc cover of a fibre product implies
agreement on the fibre product itself. -/
theorem sameRestriction_of_fpqcCovering {F : X.Modules} [F.IsQuasicoherent]
    {Y Z : AlgebraicSpace S} {fY : Y ⟶ X} {fZ : Z ⟶ X}
    (QY : Quotient ((Modules.pullback fY).obj F))
    (QZ : Quotient ((Modules.pullback fZ).obj F))
    {L : Type w} {cover : L → Over (Limits.pullback fY fZ)}
    (hcover : FpqcCovering cover)
    (h : ∀ ℓ, sameRestriction QY QZ
      ((cover ℓ).hom ≫ Limits.pullback.fst fY fZ)
      ((cover ℓ).hom ≫ Limits.pullback.snd fY fZ)
      (overlap_w (cover ℓ).hom)) :
    sameRestriction QY QZ (Limits.pullback.fst fY fZ) (Limits.pullback.snd fY fZ)
      Limits.pullback.condition := sorry

/-- A map of quasi-coherent modules that pulls back to an epimorphism along every
member of an fpqc covering is an epimorphism. -/
theorem epi_of_fpqcCovering_pullback_epi {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {F Q : X.Modules} [F.IsQuasicoherent]
    [Q.IsQuasicoherent] (φ : F ⟶ Q)
    (h : ∀ i, Epi ((Modules.pullback (family i).hom).map φ)) : Epi φ := sorry

/-- A family of quasi-coherent quotients of `f_i^* F` that restrict to the same
quotient on each given overlap covering of `X_i ×_X X_j`. -/
structure CompatibleFamily {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] where
  /-- The component quotient of `f_i^* F`. -/
  quot : ∀ i, Quotient ((Modules.pullback (family i).hom).obj F)
  /-- Component quotients restrict to the same quotient on each `X_ijk`. -/
  compatible : ∀ i j (k : K i j),
    sameRestriction (quot i) (quot j)
      ((overlap i j k).hom ≫ Limits.pullback.fst (family i).hom (family j).hom)
      ((overlap i j k).hom ≫ Limits.pullback.snd (family i).hom (family j).hom)
      (overlap_w (overlap i j k).hom)

namespace CompatibleFamily

/-- Assemble a compatible family from component quotients and overlap agreement. -/
def of {I : Type v} {family : I → Over X} (hfamily : FpqcCovering family)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent]
    (quot : ∀ i, Quotient ((Modules.pullback (family i).hom).obj F))
    (compatible : ∀ i j (k : K i j),
      sameRestriction (quot i) (quot j)
        ((overlap i j k).hom ≫ Limits.pullback.fst (family i).hom (family j).hom)
        ((overlap i j k).hom ≫ Limits.pullback.snd (family i).hom (family j).hom)
        (overlap_w (overlap i j k).hom)) :
    CompatibleFamily hfamily overlap hoverlap F where
  quot := quot
  compatible := compatible

/-- A compatible family is a family of quasi-coherent quotients with the same
restriction on each overlap. -/
theorem spec {I : Type v} {family : I → Over X} {hfamily : FpqcCovering family}
    {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom)}
    {hoverlap : ∀ i j, FpqcCovering (overlap i j)}
    {F : X.Modules} [F.IsQuasicoherent]
    (A : CompatibleFamily hfamily overlap hoverlap F) :
    ∀ i j (k : K i j),
      sameRestriction (A.quot i) (A.quot j)
        ((overlap i j k).hom ≫ Limits.pullback.fst (family i).hom (family j).hom)
        ((overlap i j k).hom ≫ Limits.pullback.snd (family i).hom (family j).hom)
        (overlap_w (overlap i j k).hom) := sorry

/-- Two compatible families are identified when each pair of components has the
same kernel. -/
def Rel {I : Type v} {family : I → Over X} {hfamily : FpqcCovering family}
    {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom)}
    {hoverlap : ∀ i j, FpqcCovering (overlap i j)}
    {F : X.Modules} [F.IsQuasicoherent]
    (A B : CompatibleFamily hfamily overlap hoverlap F) : Prop :=
  ∀ i, Quotient.Rel (A.quot i) (B.quot i)

/-- Componentwise kernel equality is an equivalence relation on compatible families. -/
theorem rel_isEquivalence {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    Equivalence
      (fun A B : CompatibleFamily hfamily overlap hoverlap F ↦ Rel A B) := sorry

end CompatibleFamily

/-- The setoid of compatible families modulo componentwise kernel equality. -/
def compatibleFamilySetoid {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    Setoid (CompatibleFamily hfamily overlap hoverlap F) where
  r := CompatibleFamily.Rel
  iseqv := CompatibleFamily.rel_isEquivalence hfamily overlap hoverlap F

/-- Kernel-identified compatible families of quasi-coherent quotients along the
given fpqc covering and overlap coverings. -/
def compatibleFamilies {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :=
  _root_.Quotient (compatibleFamilySetoid hfamily overlap hoverlap F)

/-- Restrict a global quasi-coherent quotient of `F` to the given covering family. -/
def restrict {I : Type v} {family : I → Over X} (hfamily : FpqcCovering family)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F) :
    CompatibleFamily hfamily overlap hoverlap F :=
  CompatibleFamily.of hfamily overlap hoverlap F
    (fun i ↦ Q.pullback (family i).hom) sorry

/-- Restriction of global quotients preserves kernel identification. -/
theorem restrict_rel {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    {F : X.Modules} [F.IsQuasicoherent] (Q₁ Q₂ : Quotient F) :
    (quotientSetoid F).r Q₁ Q₂ →
      (compatibleFamilySetoid hfamily overlap hoverlap F).r
        (restrict hfamily overlap hoverlap Q₁)
        (restrict hfamily overlap hoverlap Q₂) := sorry

/-- The restriction map on kernel-identified quasi-coherent quotients along an
fpqc covering and given overlap coverings. -/
def restrictClass {I : Type v} {family : I → Over X} (hfamily : FpqcCovering family)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    quotients F → compatibleFamilies hfamily overlap hoverlap F :=
  _root_.Quotient.map (restrict hfamily overlap hoverlap)
    (restrict_rel hfamily overlap hoverlap)

/-- Restriction of kernel-identified quasi-coherent quotients along an fpqc
covering is injective. -/
theorem restrictClass_injective {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    Function.Injective (restrictClass hfamily overlap hoverlap F) := sorry

/-- Restriction of kernel-identified quasi-coherent quotients along an fpqc
covering is surjective. -/
theorem restrictClass_surjective {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    Function.Surjective (restrictClass hfamily overlap hoverlap F) := sorry

/-- Restriction of kernel-identified quasi-coherent quotients along an fpqc
covering, with the given overlap coverings, is bijective. -/
theorem restrictClass_bijective {I : Type v} {family : I → Over X}
    (hfamily : FpqcCovering family) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    Function.Bijective (restrictClass hfamily overlap hoverlap F) := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh

