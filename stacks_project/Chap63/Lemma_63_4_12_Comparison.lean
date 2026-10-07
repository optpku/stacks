module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap63.Lemma_63_4_10
public import stacks_project.Chap63.Lemma_63_4_11
public import stacks_project.Chap63.Remark_63_3_14_Comparison
public import stacks_project.Chap63.Remark_63_4_6_Covariance_with_respect_to_open_embeddings_OpenImmersion

/-!
# Composition comparison for locally quasi-finite lower shriek

For composable locally quasi-finite scheme morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z`, mixed comparisons of Lemma 63.4.11 along a canonical
affine-over-affine covering of `Y` glue to a natural transformation
`(f ≫ g)_! ⟶ f_! ⋙ g_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]

/-- Pullback of the affine cover of `Z` along `g`, as an open covering of `Y`. -/
def separatedSourceCoverPullback : OpenCover.{u} Y :=
  Z.affineCover.pullback₁ g

/-- Canonical affine-over-affine open covering of the source of `g`. -/
def separatedSourceCoverOpenCover : OpenCover.{u} Y :=
  (OpenCover.affineRefinement (separatedSourceCoverPullback g)).openCover

/-- Members of the canonical affine-over-affine covering of the source of `g`. -/
def separatedSourceCover : (separatedSourceCoverOpenCover g).I₀ → Y.Opens :=
  fun i ↦ ((separatedSourceCoverOpenCover g).f i).opensRange

/-- Preimage covering of `X` associated to `separatedSourceCover g`. -/
abbrev sourceCover : (separatedSourceCoverOpenCover g).I₀ → X.Opens :=
  fun i ↦ f ⁻¹ᵁ separatedSourceCover g i

/-- Open immersions of an open of `X` composed with `f ≫ g` remain locally
quasi-finite. -/
instance locallyQuasiFinite_opens_comp (U : X.Opens) :
    LocallyQuasiFinite ((U.ι ≫ f) ≫ g) :=
  sorry

/-- Open immersions of an open of `X` composed with `f ≫ g` remain locally
of finite type. -/
instance locallyOfFiniteType_opens_comp (U : X.Opens) :
    LocallyOfFiniteType ((U.ι ≫ f) ≫ g) :=
  sorry

/-- Right-associated form of `locallyQuasiFinite_opens_comp`. -/
instance locallyQuasiFinite_opens_comp_assoc (U : X.Opens) :
    LocallyQuasiFinite (U.ι ≫ (f ≫ g)) :=
  sorry

/-- Right-associated form of `locallyOfFiniteType_opens_comp`. -/
instance locallyOfFiniteType_opens_comp_assoc (U : X.Opens) :
    LocallyOfFiniteType (U.ι ≫ (f ≫ g)) :=
  sorry

/-- Restrictions of `g` to members of `separatedSourceCover` are separated. -/
instance isSeparated_separatedSourceCover
    (i : (separatedSourceCoverOpenCover g).I₀) :
    IsSeparated ((separatedSourceCover g i).ι ≫ g) :=
  sorry

/-- Restrictions of `g` to members of `separatedSourceCover` are locally of
finite type. -/
instance locallyOfFiniteType_separatedSourceCover
    (i : (separatedSourceCoverOpenCover g).I₀) :
    LocallyOfFiniteType ((separatedSourceCover g i).ι ≫ g) :=
  sorry

/-- The restricted composite `(f ∣_ U) ≫ U.ι ≫ g` is locally quasi-finite. -/
instance locallyQuasiFinite_morphismRestrict_comp
    (i : (separatedSourceCoverOpenCover g).I₀) :
    LocallyQuasiFinite
      ((f ∣_ separatedSourceCover g i) ≫ ((separatedSourceCover g i).ι ≫ g)) :=
  sorry

/-- The restricted composite `(f ∣_ U) ≫ U.ι ≫ g` is locally of finite type. -/
instance locallyOfFiniteType_morphismRestrict_comp
    (i : (separatedSourceCoverOpenCover g).I₀) :
    LocallyOfFiniteType
      ((f ∣_ separatedSourceCover g i) ≫ ((separatedSourceCover g i).ι ≫ g)) :=
  sorry

/-- Auxiliary associativity used to identify the restricted composite with the
preimage composite. -/
theorem morphismRestrict_ι_assoc (U : Y.Opens) :
    (f ∣_ U) ≫ (U.ι ≫ g) = (f ⁻¹ᵁ U).ι ≫ (f ≫ g) :=
  sorry

/-- Exact locally quasi-finite instance for the source-cover composite. -/
instance locallyQuasiFinite_sourceCover_comp
    (i : (separatedSourceCoverOpenCover g).I₀) :
    LocallyQuasiFinite ((sourceCover f g i).ι ≫ f ≫ g) :=
  sorry

/-- Compact-support direct image is unchanged by rewriting
`(f ∣_ U) ≫ U.ι ≫ g` as `(f ⁻¹ᵁ U).ι ≫ f ≫ g`. -/
def lowerShriekFunctorComp_restrictCongr
    (i : (separatedSourceCoverOpenCover g).I₀) :
    lowerShriek ((f ∣_ separatedSourceCover g i) ≫
        ((separatedSourceCover g i).ι ≫ g)) ≅
      lowerShriek ((sourceCover f g i).ι ≫ f ≫ g) :=
  lowerShriekCongr.{u} (morphismRestrict_ι_assoc f g (separatedSourceCover g i))

/-- Base-change identification of `f_!` along an open immersion of the target. -/
def lowerShriekFunctorComp_restrictPullback
    (U : Y.Opens) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback U.ι).obj ((lowerShriek f).obj F) ≅
      (lowerShriek (f ∣_ U)).obj ((etaleAbelianSheafPullback (f ⁻¹ᵁ U).ι).obj F) :=
  (lowerShriekBaseChangeIso f U.ι (f ∣_ U) (f ⁻¹ᵁ U).ι
      (isPullback_morphismRestrict f U).flip).app F

/-- Locality of `f_!` on an open of the base: `f_{U,!}(F|_{X_U}) ≅ (f_! F)|_U`. -/
def lowerShriekFunctorComp_restrictIso
    (U : Y.Opens) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek (f ∣_ U)).obj
        ((etaleRestrictionSheaf (f ⁻¹ᵁ U).ι AddCommGrpCat.{u}).obj F) ≅
      (etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj
        ((lowerShriek f).obj F) :=
  (lowerShriek (f ∣_ U)).mapIso
      (etaleRestrictionSheafIsoPullback_app (f ⁻¹ᵁ U).ι F) ≪≫
    (lowerShriekFunctorComp_restrictPullback f U F).symm ≪≫
    (etaleRestrictionSheafIsoPullback_app U.ι ((lowerShriek f).obj F)).symm

/-- Mixed comparison of Lemma 63.4.11 on one member of the canonical covering,
followed by locality of `f_!` and covariance of `g_!` along the open
immersion. -/
def lowerShriekFunctorComp_summand
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

/-- Degree-zero coproduct of restricted compact-support direct images of
`f ≫ g` along `sourceCover`. -/
def lowerShriekFunctorComp_coverTerm
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} :=
  ∐ fun i : (separatedSourceCoverOpenCover g).I₀ ↦
    (lowerShriek ((sourceCover f g i).ι ≫ (f ≫ g))).obj
      ((etaleRestrictionSheaf (sourceCover f g i).ι AddCommGrpCat.{u}).obj F)

/-- Coproduct of the mixed comparisons on the canonical covering. -/
def lowerShriekFunctorComp_coverDesc
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekFunctorComp_coverTerm f g F ⟶
      (lowerShriek g).obj ((lowerShriek f).obj F) :=
  Sigma.desc (lowerShriekFunctorComp_summand f g F)

/-- Čech-style augmentation from the covering coproduct to `(f ≫ g)_! F`. -/
def lowerShriekFunctorComp_augmentation
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekFunctorComp_coverTerm f g F ⟶ (lowerShriek (f ≫ g)).obj F :=
  Sigma.desc fun i ↦
    (lowerShriekOpenImmersion_opens (sourceCover f g i) (f ≫ g)).app F

/-- The covering augmentation is an epimorphism, by Lemma 63.4.7. -/
instance lowerShriekFunctorComp_augmentation_epi
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Epi (lowerShriekFunctorComp_augmentation f g F) :=
  sorry

/-- The mixed covering comparison vanishes on the kernel of the augmentation. -/
theorem lowerShriekFunctorComp_kernel
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    kernel.ι (lowerShriekFunctorComp_augmentation f g F) ≫
      lowerShriekFunctorComp_coverDesc f g F = 0 :=
  sorry

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
  sorry

/-- The coproduct of mixed covering comparisons is an epimorphism, by the
mixed isomorphisms of Lemma 63.4.11 and locality of `g_!`. -/
instance lowerShriekFunctorComp_coverDesc_epi
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Epi (lowerShriekFunctorComp_coverDesc f g F) :=
  sorry

/-- Dual Čech vanishing: the covering augmentation vanishes on the kernel of
the mixed covering comparison. -/
theorem lowerShriekFunctorCompInv_kernel
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    kernel.ι (lowerShriekFunctorComp_coverDesc f g F) ≫
      lowerShriekFunctorComp_augmentation f g F = 0 :=
  sorry

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
  sorry

section mixed

variable [IsSeparated g]

/-- Left-hand path of mixed agreement: the two-lqf comparison, then
identification of `g_!` with the separated construction. -/
def lowerShriekFunctorCompIso_mixed_left :
    lowerShriek (f ≫ g) ⟶ lowerShriek f ⋙ etaleLowerShriek g :=
  lowerShriekFunctorComp f g ≫
    whiskerLeft (lowerShriek f) (lowerShriekIso_separated g).hom

/-- Right-hand path of mixed agreement: the mixed comparison of
Lemma 63.4.11. -/
def lowerShriekFunctorCompIso_mixed_right :
    lowerShriek (f ≫ g) ⟶ lowerShriek f ⋙ etaleLowerShriek g :=
  lowerShriekComp f g

end mixed

section separated

variable [IsSeparated f] [IsSeparated g]

/-- Left-hand path of separated agreement: identify `(f ≫ g)_!` with the
separated construction, then apply the inverse of Lemma 63.3.13. -/
def lowerShriekFunctorCompIso_separated_left :
    lowerShriek (f ≫ g) ⟶ etaleLowerShriek f ⋙ etaleLowerShriek g :=
  (lowerShriekIso_separated (f ≫ g)).hom ≫ (etaleLowerShriekCompIso f g).inv

/-- Right-hand path of separated agreement: the two-lqf comparison, then
identifications of `f_!` and `g_!` with the separated constructions. -/
def lowerShriekFunctorCompIso_separated_right :
    lowerShriek (f ≫ g) ⟶ etaleLowerShriek f ⋙ etaleLowerShriek g :=
  lowerShriekFunctorComp f g ≫
    whiskerRight (lowerShriekIso_separated f).hom (lowerShriek g) ≫
    whiskerLeft (etaleLowerShriek f) (lowerShriekIso_separated g).hom

end separated

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

/-- `lowerShriek` depends only on the underlying morphism, so it is unchanged
by reassociation of a triple composite. -/
theorem lowerShriek_assoc :
    lowerShriek ((f ≫ g) ≫ h) = lowerShriek (f ≫ g ≫ h) :=
  sorry

/-- Left-then-bottom path of the associativity square. -/
def lowerShriekFunctorCompIso_assoc_left :
    lowerShriek ((f ≫ g) ≫ h) ⟶
      lowerShriek f ⋙ lowerShriek g ⋙ lowerShriek h :=
  lowerShriekFunctorComp (f ≫ g) h ≫
    whiskerRight (lowerShriekFunctorComp f g) (lowerShriek h) ≫
    (associator (lowerShriek f) (lowerShriek g) (lowerShriek h)).hom

/-- Top-then-right path of the associativity square. -/
def lowerShriekFunctorCompIso_assoc_right :
    lowerShriek (f ≫ g ≫ h) ⟶
      lowerShriek f ⋙ lowerShriek g ⋙ lowerShriek h :=
  lowerShriekFunctorComp f (g ≫ h) ≫
    whiskerLeft (lowerShriek f) (lowerShriekFunctorComp g h)

end assoc

section baseChange

variable {X' Y' Z' : Scheme.{u}}
variable (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
variable (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [HasCoproducts.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]

/-- Two-step path of the pasted base-change square: the two-lqf comparison,
then the lower base change of `g`, then the upper base change of `f`. -/
def lowerShriekFunctorCompIso_baseChange_inner :
    lowerShriek (f ≫ g) ⋙ etaleAbelianSheafPullback a ⟶
      etaleAbelianSheafPullback c ⋙ lowerShriek f' ⋙ lowerShriek g' :=
  whiskerRight (lowerShriekFunctorComp f g) (etaleAbelianSheafPullback a) ≫
    (associator (lowerShriek f) (lowerShriek g) (etaleAbelianSheafPullback a)).hom ≫
    whiskerLeft (lowerShriek f) (lowerShriekBaseChange g a g' b h_lower) ≫
    (associator (lowerShriek f) (etaleAbelianSheafPullback b) (lowerShriek g')).inv ≫
    whiskerRight (lowerShriekBaseChange f b f' c h_upper) (lowerShriek g') ≫
    (associator (etaleAbelianSheafPullback c) (lowerShriek f') (lowerShriek g')).hom

/-- Outer path of the pasted base-change square: base change of `f ≫ g` along
the pasted cartesian square, then the two-lqf comparison of `f'` and `g'`. -/
def lowerShriekFunctorCompIso_baseChange_outer :
    lowerShriek (f ≫ g) ⋙ etaleAbelianSheafPullback a ⟶
      etaleAbelianSheafPullback c ⋙ lowerShriek f' ⋙ lowerShriek g' :=
  lowerShriekBaseChange (f ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) ≫
    whiskerLeft (etaleAbelianSheafPullback c) (lowerShriekFunctorComp f' g')

end baseChange

end AlgebraicGeometry.Scheme.Etale

end
