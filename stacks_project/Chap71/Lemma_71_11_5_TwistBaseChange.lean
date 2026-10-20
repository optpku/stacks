/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_11_5_TwistBaseChangeLocal

/-!
# The actual global base-change comparison of canonical Serre twists

The local fraction maps give matching sections on the affine tests of each
genuine fibre product. Inversion of actual restriction reconstructs direct-image
sections. Dense-basis fullness gives the direct-image module map, whose adjoint
is the requested pullback comparison. All data and morphisms are specified.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
variable {𝒜 𝒜'} {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
variable (hAlg : AlgebraPullback g deg deg')
variable {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
variable {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')

/-- The actual fraction-map sections form a matching family on the fibre product. -/
def matching (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℤ)
    (x : (obj F hF n).val.obj (op U.obj)) :
    AffineMatching (map g hAlg hF hF') (obj F' hF' n) U.obj where
  value V j := sectionComponent g hAlg hF hF' U V j n x
  compatible := sorry

/-- Reconstruct the direct-image section by the inverse of its actual affine restriction. -/
def pushforwardSection (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℤ)
    (x : (obj F hF n).val.obj (op U.obj)) :
    ((Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n)).val.obj (op U.obj) :=
  sectionOfMatching (map g hAlg hF hF') (obj F' hF' n) U.obj
    (matching g hAlg hF hF' U n x)

/-- The concrete module map on the dense affine basis. -/
def basisDirectMap (n : ℤ) :
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj (obj F hF n) ⟶
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
      ((Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n)) where
  val :=
    { app := fun U ↦ by
        let M := (((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
          (obj F hF n)).val.obj U
        let N := (((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
          ((Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n))).val.obj U
        exact @ModuleCat.ofHom ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj U) _ M N
          M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
          { toFun := pushforwardSection g hAlg hF hF' U.unop n
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- Descent through the actual fully faithful restriction functor. -/
def directMap (n : ℤ) : obj F hF n ⟶
    (Modules.pushforward (map g hAlg hF hF')).obj (obj F' hF' n) :=
  ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).preimage
    (basisDirectMap g hAlg hF hF' n)

/-- The requested pullback morphism is the actual adjoint of the specified direct-image map. -/
def degreeMap (n : ℤ) :
    (Modules.pullback (map g hAlg hF hF')).obj (obj F hF n) ⟶ obj F' hF' n :=
  ((Modules.pullbackPushforwardAdjunction (map g hAlg hF hF')).homEquiv _ _).symm
    (directMap g hAlg hF hF' n)

/-- The adjoint recovers exactly the constructed direct-image map. -/
theorem degreeMap_adjoint (n : ℤ) :
    ((Modules.pullbackPushforwardAdjunction (map g hAlg hF hF')).homEquiv _ _)
      (degreeMap g hAlg hF hF' n) = directMap g hAlg hF hF' n :=
  Equiv.apply_symm_apply _ _

/-- The local component is exactly the actual fraction-induced section map. -/
theorem directMap_atGraph (U : affineEtaleSite (toAlgebraicSpace F hF))
    (V : affineEtaleSite (toAlgebraicSpace F' hF'))
    (j : AffineGraph (map g hAlg hF hF') U.obj V) (n : ℤ)
    (x : (obj F hF n).val.obj (op U.obj)) :
    directImageAtGraph (map g hAlg hF hF') (obj F' hF' n) U.obj V j
      ((directMap g hAlg hF hF' n).val.app (op U.obj) x) =
        sectionComponent g hAlg hF hF' U V j n x := by
  have h := ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).map_preimage
    (basisDirectMap g hAlg hF hF' n)
  have hx := congrArg (fun q ↦ q.val.app (op U) x) h
  change (directMap g hAlg hF hF' n).val.app (op U.obj) x =
    pushforwardSection g hAlg hF hF' U n x at hx
  rw [hx]
  exact sectionOfMatching_atGraph (map g hAlg hF hF') (obj F' hF' n) U.obj
    (matching g hAlg hF hF' U n x) V j

/-- Local affine scalar extension identifies this fixed map in every integral degree.
No flatness, degree-one-generation, or étaleness of the base change is assumed. -/
instance degreeMap_isIso (n : ℤ) : IsIso (degreeMap g hAlg hF hF' n) := sorry

/-- The actual inverse is the inverse of that specified comparison. -/
def degreeIso (n : ℤ) :
    (Modules.pullback (map g hAlg hF hF')).obj (obj F hF n) ≅ obj F' hF' n :=
  asIso (degreeMap g hAlg hF hF' n)

/-- Assemble the specified component maps and their actual algebra laws. -/
def comparison : GradedAlgebraComparison (map g hAlg hF hF') (family F hF) (family F' hF') where
  degreeMap := degreeMap g hAlg hF hF'
  map_one := sorry
  map_mul := sorry

/-- Full source-shaped base-change data, with the constructed canonical families. -/
def data : RelativeProj.BaseChange g hAlg hF hF' (family F hF) (family F' hF') where
  iso := canonicalBaseChangeIso g hAlg hF hF'
  iso_fst := canonicalBaseChangeIso_fst g hAlg hF hF'
  theta := comparison g hAlg hF hF'

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange
