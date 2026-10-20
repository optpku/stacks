/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Properties

/-!
# Composition of locally quasi-finite compact-support direct images

Mixed composition comparisons on an affine-over-affine covering descend to
mutually inverse natural transformations. The resulting composition isomorphism
is compatible with separated composition, geometric stalks, associativity,
and cartesian base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Pullback of the affine cover of `Z` along `g`, as an open covering of `Y`. -/
private def separatedSourceCoverPullback : OpenCover.{u} Y :=
  Z.affineCover.pullback₁ g

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Canonical affine-over-affine open covering of the source of `g`. -/
private def separatedSourceCoverOpenCover : OpenCover.{u} Y :=
  (OpenCover.affineRefinement (separatedSourceCoverPullback g)).openCover

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Members of the canonical affine-over-affine covering of the source of `g`. -/
private def separatedSourceCover : (separatedSourceCoverOpenCover g).I₀ → Y.Opens :=
  fun i ↦ ((separatedSourceCoverOpenCover g).f i).opensRange

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Preimage covering of `X` associated to `separatedSourceCover g`. -/
private abbrev sourceCover : (separatedSourceCoverOpenCover g).I₀ → X.Opens :=
  fun i ↦ f ⁻¹ᵁ separatedSourceCover g i

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Restrictions of `g` to members of `separatedSourceCover` are separated. -/
private instance isSeparated_separatedSourceCover
    (i : (separatedSourceCoverOpenCover g).I₀) :
    IsSeparated ((separatedSourceCover g i).ι ≫ g) :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Compact-support direct image is unchanged by rewriting
`(f ∣_ U) ≫ U.ι ≫ g` as `(f ⁻¹ᵁ U).ι ≫ f ≫ g`. -/
private def lowerShriekFunctorComp_restrictCongr
    (i : (separatedSourceCoverOpenCover g).I₀) :
    lowerShriek ((f ∣_ separatedSourceCover g i) ≫
        ((separatedSourceCover g i).ι ≫ g)) ≅
      lowerShriek ((sourceCover f g i).ι ≫ f ≫ g) :=
  lowerShriekCongr.{u} (AlgebraicGeometry.morphismRestrict_ι_assoc f (separatedSourceCover g i) g)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Base-change identification of `f_!` along an open immersion of the target. -/
private def lowerShriekFunctorComp_restrictPullback
    (U : Y.Opens) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback U.ι).obj ((lowerShriek f).obj F) ≅
      (lowerShriek (f ∣_ U)).obj ((etaleAbelianSheafPullback (f ⁻¹ᵁ U).ι).obj F) :=
  (lowerShriekBaseChangeIso f U.ι (f ∣_ U) (f ⁻¹ᵁ U).ι
      (isPullback_morphismRestrict f U).flip).app F

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Locality of `f_!` on an open of the base: `f_{U,!}(F|_{X_U}) ≅ (f_! F)|_U`. -/
private def lowerShriekFunctorComp_restrictIso
    (U : Y.Opens) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f ∣_ U)).obj
        ((etaleRestrictionSheaf (f ⁻¹ᵁ U).ι AddCommGrpCat.{u}).obj F) ≅
      (etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj
        ((lowerShriek f).obj F) :=
  (lowerShriek (f ∣_ U)).mapIso
      (etaleRestrictionSheafIsoPullback_app (f ⁻¹ᵁ U).ι F) ≪≫
    (lowerShriekFunctorComp_restrictPullback f U F).symm ≪≫
    (etaleRestrictionSheafIsoPullback_app U.ι ((lowerShriek f).obj F)).symm

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Mixed composition comparison on one member of the canonical covering,
followed by locality of `f_!` and covariance of `g_!` along the open
immersion. -/
private def lowerShriekFunctorComp_summand
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (i : (separatedSourceCoverOpenCover g).I₀) :
    (lowerShriek ((sourceCover f g i).ι ≫ (f ≫ g))).obj
        ((etaleRestrictionSheaf (sourceCover f g i).ι AddCommGrpCat.{u}).obj F) ⟶
      (lowerShriek g).obj ((lowerShriek f).obj F) :=
  (lowerShriekFunctorComp_restrictCongr f g i).inv.app
      ((etaleRestrictionSheaf (sourceCover f g i).ι AddCommGrpCat.{u}).obj F) ≫
    (lowerShriekComp (f ∣_ separatedSourceCover g i)
        ((separatedSourceCover g i).ι ≫ g)).app
      ((etaleRestrictionSheaf (sourceCover f g i).ι AddCommGrpCat.{u}).obj F) ≫
    (etaleLowerShriek ((separatedSourceCover g i).ι ≫ g)).map
      (lowerShriekFunctorComp_restrictIso f (separatedSourceCover g i) F).hom ≫
    (lowerShriekIso_separated ((separatedSourceCover g i).ι ≫ g)).inv.app
      ((etaleRestrictionSheaf (separatedSourceCover g i).ι AddCommGrpCat.{u}).obj
        ((lowerShriek f).obj F)) ≫
    (lowerShriekOpenImmersion_opens (separatedSourceCover g i) g).app
      ((lowerShriek f).obj F)

variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Degree-zero coproduct of restricted compact-support direct images of
`f ≫ g` along `sourceCover`. -/
private def lowerShriekFunctorComp_coverTerm
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} :=
  ∐ fun i : (separatedSourceCoverOpenCover g).I₀ ↦
    (lowerShriek ((sourceCover f g i).ι ≫ (f ≫ g))).obj
      ((etaleRestrictionSheaf (sourceCover f g i).ι AddCommGrpCat.{u}).obj F)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Coproduct of the mixed comparisons on the canonical covering. -/
private def lowerShriekFunctorComp_coverDesc
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekFunctorComp_coverTerm f g F ⟶
      (lowerShriek g).obj ((lowerShriek f).obj F) :=
  Sigma.desc (lowerShriekFunctorComp_summand f g F)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Čech-style augmentation from the covering coproduct to `(f ≫ g)_! F`. -/
private def lowerShriekFunctorComp_augmentation
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekFunctorComp_coverTerm f g F ⟶ (lowerShriek (f ≫ g)).obj F :=
  Sigma.desc fun i ↦
    (lowerShriekOpenImmersion_opens (sourceCover f g i) (f ≫ g)).app F

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- The augmentation from the covering coproduct is an epimorphism. -/
private instance lowerShriekFunctorComp_augmentation_epi
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Epi (lowerShriekFunctorComp_augmentation f g F) :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- The mixed covering comparison vanishes on the kernel of the augmentation. -/
private theorem lowerShriekFunctorComp_kernel
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    kernel.ι (lowerShriekFunctorComp_augmentation f g F) ≫
      lowerShriekFunctorComp_coverDesc f g F = 0 :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose the private descent construction in this public map.
set_option backward.privateInPublic true in
/-- Objectwise comparison `(f ≫ g)_! F ⟶ g_! (f_! F)`, obtained by descending
the mixed covering maps along the Čech augmentation. -/
def lowerShriekFunctorComp_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f ≫ g)).obj F ⟶
      (lowerShriek g).obj ((lowerShriek f).obj F) :=
  Abelian.epiDesc (lowerShriekFunctorComp_augmentation f g F)
    (lowerShriekFunctorComp_coverDesc f g F)
    (lowerShriekFunctorComp_kernel f g F)

/-- Canonical comparison `(g ∘ f)_! ⟶ g_! ∘ f_!` of functors on abelian étale
sheaves. -/
def lowerShriekFunctorComp :
    lowerShriek (f ≫ g) ⟶ lowerShriek f ⋙ lowerShriek g where
  app := lowerShriekFunctorComp_app f g
  naturality := sorry

/-- Evaluating the comparison at an abelian étale sheaf recovers the descended
covering map. -/
theorem lowerShriekFunctorComp_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekFunctorComp f g).app F = lowerShriekFunctorComp_app f g F :=
  rfl

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- The coproduct of the mixed covering comparisons is an epimorphism. -/
private instance lowerShriekFunctorComp_coverDesc_epi
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Epi (lowerShriekFunctorComp_coverDesc f g F) :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private dependency of the public descended maps.
set_option backward.privateInPublic true in
/-- Dual Čech vanishing: the covering augmentation vanishes on the kernel of
the mixed covering comparison. -/
private theorem lowerShriekFunctorCompInv_kernel
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    kernel.ι (lowerShriekFunctorComp_coverDesc f g F) ≫
      lowerShriekFunctorComp_augmentation f g F = 0 :=
  sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose the private descent construction in this public map.
set_option backward.privateInPublic true in
/-- Objectwise inverse comparison `g_! (f_! F) ⟶ (f ≫ g)_! F`, obtained by
dual Čech descent of the covering augmentation along the mixed covering
comparison. -/
def lowerShriekFunctorCompInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek g).obj ((lowerShriek f).obj F) ⟶
      (lowerShriek (f ≫ g)).obj F :=
  Abelian.epiDesc (lowerShriekFunctorComp_coverDesc f g F)
    (lowerShriekFunctorComp_augmentation f g F)
    (lowerShriekFunctorCompInv_kernel f g F)

/-- Canonical inverse comparison `g_! ∘ f_! ⟶ (g ∘ f)_!` of functors on
abelian étale sheaves, by dual Čech descent. -/
def lowerShriekFunctorCompInv :
    lowerShriek f ⋙ lowerShriek g ⟶ lowerShriek (f ≫ g) where
  app := lowerShriekFunctorCompInv_app f g
  naturality := sorry

/-- Evaluating the inverse comparison at an abelian étale sheaf recovers the
dual descended covering map. -/
theorem lowerShriekFunctorCompInv_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekFunctorCompInv f g).app F =
      lowerShriekFunctorCompInv_app f g F :=
  rfl

variable (zbar : GeometricPoint Z)

/-- Reindexing of fibrewise stalk coproducts along `Fiber.compEquiv`, using the
stalk formula for `f`. -/
def abelianStalkCoproductCompIso :
    lowerShriek f ⋙ abelianStalkCoproduct g zbar ≅
      abelianStalkCoproduct (f ≫ g) zbar :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          Sigma.desc fun y : Fiber g zbar ↦
            ((lowerShriekStalkIso f y.point).app F).hom ≫
              Sigma.desc fun x : Fiber f y.point ↦
                Sigma.ι
                  (fun w : Fiber (f ≫ g) zbar ↦
                    (toSmallEtalePoint w.point).sheafFiber.obj F)
                  ((Fiber.compEquiv f g zbar).symm ⟨y, x⟩)
        inv :=
          Sigma.desc fun w : Fiber (f ≫ g) zbar ↦
            Sigma.ι
                (fun x : Fiber f (Fiber.compEquiv f g zbar w).1.point ↦
                  (toSmallEtalePoint x.point).sheafFiber.obj F)
                (Fiber.compEquiv f g zbar w).2 ≫
              ((lowerShriekStalkIso f
                  (Fiber.compEquiv f g zbar w).1.point).app F).inv ≫
                Sigma.ι
                  (fun y : Fiber g zbar ↦
                    (toSmallEtalePoint y.point).sheafFiber.obj
                      ((lowerShriek f).obj F))
                  (Fiber.compEquiv f g zbar w).1
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The forward map of `abelianStalkCoproductCompIso` is the coproduct of stalk
identifications of `f`, reindexed by `Fiber.compEquiv`. -/
theorem abelianStalkCoproductCompIso_hom
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproductCompIso f g zbar).hom.app F =
      Sigma.desc fun y : Fiber g zbar ↦
        ((lowerShriekStalkIso f y.point).app F).hom ≫
          Sigma.desc fun x : Fiber f y.point ↦
            Sigma.ι
              (fun w : Fiber (f ≫ g) zbar ↦
                (toSmallEtalePoint w.point).sheafFiber.obj F)
              ((Fiber.compEquiv f g zbar).symm ⟨y, x⟩) :=
  rfl

/-- Compact-support direct image along a composite of locally quasi-finite morphisms
is canonically isomorphic to the composite of the compact-support direct images. -/
def lowerShriekFunctorCompIso :
    lowerShriek (f ≫ g) ≅ lowerShriek f ⋙ lowerShriek g where
  hom := lowerShriekFunctorComp f g
  inv := lowerShriekFunctorCompInv f g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The objectwise identification `(f ≫ g)_! F ≅ g_! (f_! F)` at an abelian
étale sheaf `F`. -/
def lowerShriekFunctorCompIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f ≫ g)).obj F ≅
      (lowerShriek g).obj ((lowerShriek f).obj F) :=
  (lowerShriekFunctorCompIso f g).app F

/-- The forward map of `lowerShriekFunctorCompIso` is the constructed
composition comparison. -/
theorem lowerShriekFunctorCompIso_hom :
    (lowerShriekFunctorCompIso f g).hom = lowerShriekFunctorComp f g :=
  rfl

/-- The inverse map of `lowerShriekFunctorCompIso` is the dual Čech
descent comparison. -/
theorem lowerShriekFunctorCompIso_inv :
    (lowerShriekFunctorCompIso f g).inv = lowerShriekFunctorCompInv f g :=
  rfl

section separated

variable [IsSeparated f] [IsSeparated g]

/-- For separated morphisms, the composition isomorphism agrees with the
separated compact-support composition isomorphism. -/
theorem lowerShriekFunctorCompIso_separated :
    ((lowerShriekIso_separated (f ≫ g)).hom ≫ (etaleLowerShriekCompIso f g).inv) =
      ((lowerShriekFunctorCompIso f g).hom ≫
    whiskerRight (lowerShriekIso_separated f).hom (lowerShriek g) ≫
    whiskerLeft (etaleLowerShriek f) (lowerShriekIso_separated g).hom) :=
  sorry

end separated

section mixed

variable [IsSeparated g]

/-- When the second morphism is separated, the composition isomorphism
agrees with the mixed compact-support composition comparison. -/
theorem lowerShriekFunctorCompIso_mixed :
    ((lowerShriekFunctorCompIso f g).hom ≫
    whiskerLeft (lowerShriek f) (lowerShriekIso_separated g).hom) =
      (lowerShriekComp f g) :=
  sorry

end mixed

/-- The composition isomorphism commutes with the geometric-stalk coproduct
formulas and the reindexing of geometric fibres. -/
theorem lowerShriekFunctorCompIso_stalk (zbar : GeometricPoint Z)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq (((lowerShriekStalkIso (f ≫ g) zbar).app F).hom)
      ((toSmallEtalePoint zbar).sheafFiber.map
        ((lowerShriekFunctorCompIso f g).hom.app F))
      (𝟙 ((abelianStalkCoproduct (f ≫ g) zbar).obj F))
      (((lowerShriekStalkIso g zbar).app ((lowerShriek f).obj F)).hom ≫
    (abelianStalkCoproductCompIso f g zbar).hom.app F) :=
  sorry

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

/-- The composition isomorphisms are associative for three composable
locally quasi-finite morphisms. -/
theorem lowerShriekFunctorCompIso_assoc :
    ((lowerShriekFunctorCompIso (f ≫ g) h).hom ≫
    whiskerRight ((lowerShriekFunctorCompIso f g).hom) (lowerShriek h) ≫
    (associator (lowerShriek f) (lowerShriek g) (lowerShriek h)).hom) =
      (lowerShriekCongr (Category.assoc f g h)).hom ≫
        ((lowerShriekFunctorCompIso f (g ≫ h)).hom ≫
    whiskerLeft (lowerShriek f) ((lowerShriekFunctorCompIso g h).hom)) :=
  sorry

end assoc

section baseChange

variable {X' Y' Z' : Scheme.{u}}
variable (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
variable (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [HasCoproducts.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]

/-- The composition isomorphism commutes with base change along two
vertically pasted cartesian squares. -/
theorem lowerShriekFunctorCompIso_baseChange :
    (whiskerRight ((lowerShriekFunctorCompIso f g).hom) (etaleAbelianSheafPullback a) ≫
    (associator (lowerShriek f) (lowerShriek g) (etaleAbelianSheafPullback a)).hom ≫
    whiskerLeft (lowerShriek f) (lowerShriekBaseChange g a g' b h_lower) ≫
    (associator (lowerShriek f) (etaleAbelianSheafPullback b) (lowerShriek g')).inv ≫
    whiskerRight (lowerShriekBaseChange f b f' c h_upper) (lowerShriek g') ≫
    (associator (etaleAbelianSheafPullback c) (lowerShriek f') (lowerShriek g')).hom) =
      (lowerShriekBaseChange (f ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) ≫
    whiskerLeft (etaleAbelianSheafPullback c) ((lowerShriekFunctorCompIso f' g').hom)) :=
  sorry

end baseChange

end AlgebraicGeometry.Scheme.Etale

end
