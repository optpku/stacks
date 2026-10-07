module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_20_1_ProjectiveSpace
public import stacks_project.Chap69.Lemma_69_20_1_Tensor

/-!
# The twisting sheaf `𝒪(1)` on projective space over an algebraic space

The sheaf `𝒪_{P^n_Y}(1)` is the pullback of the étale transfer of the scheme-level
`𝒪_{P^n_S}(1)`, itself the pullback of the standard twisting sheaf on `P^n_ℤ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme-level sheaf `𝒪_{P^n_S}(1)`, obtained by pulling back the standard twisting
sheaf on `P^n` over `ℤ`. -/
def twistingSheafScheme (n : ℕ) (S : Scheme.{u}) :
    (AlgebraicGeometry.ProjectiveSpace n S).Modules :=
  (Scheme.Modules.pullback
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.ProjectiveSpace.scheme (ULift.{u} ℤ) n)))).obj
    (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ULift.{u} ℤ) n 1)

/-- The structure morphism of an étale object over `ofScheme n S` as a morphism of schemes
into `P^n_S`. -/
def twistingSheafSchemeHom (n : ℕ) (S : Scheme.{u})
    (U : smallEtaleSite (ofScheme n S)) :
    U.left.left ⟶ AlgebraicGeometry.ProjectiveSpace n S :=
  (toOverHom U.hom).left

/-- A morphism of étale objects over `ofScheme n S` is compatible with the structure
morphisms to `P^n_S`. -/
theorem twistingSheafSchemeHom_comp (n : ℕ) (S : Scheme.{u})
    {U V : smallEtaleSite (ofScheme n S)} (f : U ⟶ V) :
    f.left.left ≫ twistingSheafSchemeHom n S V = twistingSheafSchemeHom n S U :=
  sorry

/-- The morphism of schemes over `P^n_S` induced by a morphism of the small étale site of
`ofScheme n S`, using the stored costructured-arrow triangle. -/
def ofSchemeEtaleToOverHom (n : ℕ) (S : Scheme.{u})
    {U V : smallEtaleSite (ofScheme n S)} (f : U ⟶ V) :
    Over.mk (twistingSheafSchemeHom n S U) ⟶ Over.mk (twistingSheafSchemeHom n S V) :=
  Over.homMk f.left.left <|
    congrArg
      (fun φ : U.left ⟶ Over.mk (AlgebraicGeometry.ProjectiveSpace.toBase n S) => φ.left)
      ((congrArg (fun x => x ≫ toOverHom V.hom)
          (Yoneda.fullyFaithful.preimage_map f.left).symm).trans
        ((Yoneda.fullyFaithful.preimage_comp (yoneda.map f.left) V.hom).symm.trans
          (congrArg toOverHom (f.w.trans (Category.comp_id U.hom)))))

/-- The functor sending an étale object over `ofScheme n S` to its structure morphism into
`P^n_S`. -/
def ofSchemeEtaleToOver (n : ℕ) (S : Scheme.{u}) :
    smallEtaleSite (ofScheme n S) ⥤
      CategoryTheory.Over (AlgebraicGeometry.ProjectiveSpace n S) where
  obj U := Over.mk (twistingSheafSchemeHom n S U)
  map f := ofSchemeEtaleToOverHom n S f
  map_id := sorry
  map_comp := sorry

/-- The object map of `ofSchemeEtaleToOver` is `Over.mk` of the structure morphism to
`P^n_S`. -/
theorem ofSchemeEtaleToOver_obj (n : ℕ) (S : Scheme.{u})
    (U : smallEtaleSite (ofScheme n S)) :
    (ofSchemeEtaleToOver n S).obj U = Over.mk (twistingSheafSchemeHom n S U) :=
  rfl

/-- The underlying scheme morphism of `ofSchemeEtaleToOverHom` is the site morphism on
underlying schemes. -/
theorem ofSchemeEtaleToOverHom_left (n : ℕ) (S : Scheme.{u})
    {U V : smallEtaleSite (ofScheme n S)} (f : U ⟶ V) :
    (ofSchemeEtaleToOverHom n S f).left = f.left.left :=
  rfl

/-- The morphism map of `ofSchemeEtaleToOver` is `ofSchemeEtaleToOverHom`. -/
theorem ofSchemeEtaleToOver_map (n : ℕ) (S : Scheme.{u})
    {U V : smallEtaleSite (ofScheme n S)} (f : U ⟶ V) :
    (ofSchemeEtaleToOver n S).map f = ofSchemeEtaleToOverHom n S f :=
  rfl

/-- Global sections of `(twistingSheafSchemeHom n S U)^* (twistingSheafScheme n S)`, as a
module over the small-étale structure sheaf of `ofScheme n S`. -/
noncomputable def twistingSheafOfSchemeObj (n : ℕ) (S : Scheme.{u})
    (U : (smallEtaleSite (ofScheme n S))ᵒᵖ) :
    ModuleCat ((structureSheaf (ofScheme n S)).obj.obj U) :=
  (RingedSpace.moduleGlobalSectionsFunctor U.unop.left.left.toRingedSpace).obj
    ((Scheme.Modules.pullback (twistingSheafSchemeHom n S U.unop)).obj
      (twistingSheafScheme n S))

/-- Restriction of sections of the transferred `𝒪_{P^n_S}(1)` along a morphism of the small
étale site, as a semilinear map over the small-étale structure sheaf. -/
noncomputable def twistingSheafOfSchemeMap (n : ℕ) (S : Scheme.{u})
    {U V : (smallEtaleSite (ofScheme n S))ᵒᵖ} (i : U ⟶ V) :
    twistingSheafOfSchemeObj n S U ⟶
      (ModuleCat.restrictScalars
        ((structureSheaf (ofScheme n S)).obj.map i).hom).obj
        (twistingSheafOfSchemeObj n S V) :=
  let source := twistingSheafOfSchemeObj n S U
  let target :=
    (ModuleCat.restrictScalars
      ((structureSheaf (ofScheme n S)).obj.map i).hom).obj
      (twistingSheafOfSchemeObj n S V)
  let restriction :=
    Scheme.Modules.PullbackSections.map (twistingSheafScheme n S)
      ((ofSchemeEtaleToOver n S).map i.unop)
  @ModuleCat.ofHom ((structureSheaf (ofScheme n S)).obj.obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := restriction.hom
      map_add' := restriction.hom.map_add
      map_smul' := sorry }

/-- The étale transfer of `𝒪_{P^n_S}(1)` as a presheaf of modules over the small-étale
structure sheaf of `ofScheme n S`. -/
def twistingSheafOfSchemePresheaf (n : ℕ) (S : Scheme.{u}) :
    PresheafOfModules (structureSheaf (ofScheme n S)).obj where
  obj U := twistingSheafOfSchemeObj n S U
  map i := twistingSheafOfSchemeMap n S i
  map_id := sorry
  map_comp := sorry

/-- At an étale object `U`, the transferred sheaf has value the global sections of the
pullback of `𝒪_{P^n_S}(1)` along the structure morphism of `U`. -/
theorem twistingSheafOfSchemePresheaf_obj (n : ℕ) (S : Scheme.{u})
    (U : (smallEtaleSite (ofScheme n S))ᵒᵖ) :
    (twistingSheafOfSchemePresheaf n S).obj U = twistingSheafOfSchemeObj n S U :=
  rfl

/-- Restriction in the étale transfer of `𝒪_{P^n_S}(1)` is the canonical pullback-sections
map over the small-étale structure sheaf. -/
theorem twistingSheafOfSchemePresheaf_map (n : ℕ) (S : Scheme.{u})
    {U V : (smallEtaleSite (ofScheme n S))ᵒᵖ} (i : U ⟶ V) :
    (twistingSheafOfSchemePresheaf n S).map i = twistingSheafOfSchemeMap n S i :=
  rfl

/-- The étale transfer of `𝒪_{P^n_S}(1)` satisfies the sheaf condition. -/
theorem twistingSheafOfSchemePresheaf_isSheaf (n : ℕ) (S : Scheme.{u}) :
    Presheaf.IsSheaf (smallEtaleTopology (ofScheme n S))
      (twistingSheafOfSchemePresheaf n S).presheaf :=
  sorry

/-- The sheaf `𝒪_{P^n_S}(1)` on `ofScheme n S`. -/
def twistingSheafOfScheme (n : ℕ) (S : Scheme.{u}) : (ofScheme n S).Modules where
  val := twistingSheafOfSchemePresheaf n S
  isSheaf := twistingSheafOfSchemePresheaf_isSheaf n S

/-- The underlying presheaf of `twistingSheafOfScheme n S` is the pullback-sections
presheaf of `𝒪_{P^n_S}(1)` over the small-étale structure sheaf. -/
theorem twistingSheafOfScheme_val (n : ℕ) (S : Scheme.{u}) :
    (twistingSheafOfScheme n S).val = twistingSheafOfSchemePresheaf n S :=
  rfl

namespace ProjectiveSpace

/-- The twisting sheaf `𝒪_{P^n_Y}(1)` on projective space over an algebraic space. -/
def twistingSheaf (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    (ProjectiveSpace n Y).Modules :=
  (Modules.pullback (toOfScheme n Y)).obj (twistingSheafOfScheme n S)

/-- `twistingSheaf n Y` is the module pullback of `𝒪_{P^n_S}(1)` along `toOfScheme`. -/
theorem twistingSheaf_spec (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    twistingSheaf n Y =
      (Modules.pullback (toOfScheme n Y)).obj (twistingSheafOfScheme n S) :=
  rfl

/-- The twisting sheaf `𝒪_{P^n_Y}(1)` is invertible. -/
instance twistingSheaf_isInvertible (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    isInvertibleObject (twistingSheaf n Y) :=
  sorry

/-- The pullback of `𝒪_{P^n_Y}(1)` along a morphism into projective space is invertible. -/
instance pullback_twistingSheaf_isInvertible {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (n : ℕ) (i : X ⟶ ProjectiveSpace n Y) :
    isInvertibleObject ((Modules.pullback i).obj (twistingSheaf n Y)) :=
  sorry

end ProjectiveSpace

end AlgebraicGeometry.AlgebraicSpace
