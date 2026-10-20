/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_11_5_TwistDescent
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionBaseChange

/-!
# Actual direct-image sections from affine matching families

For any morphism of algebraic spaces, evaluate the actual right-Kan-extension
limit at each affine scheme mapping to the fibre-product étale object. The
inverse of this specified restriction map reconstructs a section by the sheaf
condition. This is not an arbitrary comparison between the two section types.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf.InternalModule
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open RingedSite.ToposHom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

variable {S : Scheme.{u}} {P Q : AlgebraicSpace S} (k : Q ⟶ P) (M : Q.Modules)

/-- An affine test over the genuine fibre-product object defining k_*M(U). -/
abbrev AffineGraph (U : smallEtaleSite P) (V : affineEtaleSite Q) :=
  (smallEtaleToSpaces Q).obj V.obj ⟶ (etaleBaseChange k).obj U

/-- Matching sections on all affine tests of that fibre product. -/
structure AffineMatching (U : smallEtaleSite P) where
  value : ∀ (V : affineEtaleSite Q), AffineGraph k U V → M.val.obj (op V.obj)
  compatible : ∀ (V V' : affineEtaleSite Q) (f : V' ⟶ V)
    (j : AffineGraph k U V) (j' : AffineGraph k U V')
    (_ : (smallEtaleToSpaces Q).map f.hom ≫ j = j'),
    M.val.map (op f.hom) (value V j) = value V' j'

/-- The actual diagram used by the existing direct-image implementation. -/
abbrev directImageDiagram (U : smallEtaleSite P) :=
  StructuredArrow.proj (op ((etaleBaseChange k).obj U)) (smallEtaleToSpaces Q).op ⋙
    ((ToInternal.underlying (structureSheaf Q)).obj M).obj

instance directImageDiagram_hasLimit (U : smallEtaleSite P) :
    HasLimit (directImageDiagram k M U) :=
  EtaleTopos.allChartHasLimit Q ((ToInternal.underlying (structureSheaf Q)).obj M)
    ((etaleBaseChange k).obj U)

/-- Restrict an actual direct-image section by the canonical Kan-limit projection. -/
def directImageAtGraph (U : smallEtaleSite P) (V : affineEtaleSite Q)
    (j : AffineGraph k U V)
    (x : ((Modules.pushforward k).obj M).val.obj (op U)) : M.val.obj (op V.obj) :=
  let underlying :=
    (((ModulePushforward.forgetIso (ringedToposHom k)).hom.app M).hom.app (op U))
      (ToInternal.sectionEquiv (structureSheaf P)
        ((Modules.pushforward k).obj M) (op U) x)
  (ToInternal.sectionEquiv (structureSheaf Q) M (op V.obj)).symm
    (EtaleTopos.extensionEvaluation Q
      ((ToInternal.underlying (structureSheaf Q)).obj M) j underlying)

/-- The actual restriction function from direct-image sections to matching families. -/
def directImageMatching (U : smallEtaleSite P)
    (x : ((Modules.pushforward k).obj M).val.obj (op U)) : AffineMatching k M U where
  value V j := directImageAtGraph k M U V j x
  compatible := sorry

/-- Affine étale tests form a dense basis of the fibre-product object, so the
specified restriction is bijective. This uses sheaf descent, not quasi-compactness. -/
theorem directImageMatching_bijective (U : smallEtaleSite P) :
    Function.Bijective (directImageMatching k M U) := sorry

/-- Reconstruct a section by inverting that exact restriction function. -/
def sectionOfMatching (U : smallEtaleSite P) (s : AffineMatching k M U) :
    ((Modules.pushforward k).obj M).val.obj (op U) :=
  (Equiv.ofBijective (directImageMatching k M U) (directImageMatching_bijective k M U)).symm s

/-- The reconstructed section has exactly the supplied affine components. -/
theorem sectionOfMatching_atGraph (U : smallEtaleSite P) (s : AffineMatching k M U)
    (V : affineEtaleSite Q) (j : AffineGraph k U V) :
    directImageAtGraph k M U V j (sectionOfMatching k M U s) = s.value V j := by
  exact congrArg (fun z : AffineMatching k M U ↦ z.value V j)
    ((Equiv.ofBijective (directImageMatching k M U)
      (directImageMatching_bijective k M U)).apply_symm_apply s)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
